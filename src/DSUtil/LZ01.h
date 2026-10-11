/*
 * (C) 2026 see Authors.txt
 *
 * This file is part of MPC-BE.
 *
 * MPC-BE is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * MPC-BE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * ============================================================================
 *  LZ01 加密容器支持 —— 公共实现（header-only，本地补丁）
 *
 *  容器格式：  [前 N 字节 AES-256-CTR 密文][其余明文][末尾 16 字节标记]
 *  末尾标记：  "LZ01" | version(u32 大端) | N(u64 大端)        共 16 字节
 *  CTR 计数器块 = nonce(8B) || 大端 64 位块序号(8B)，从 0 开始计数。
 *
 *  为什么要有这个头文件：MPC-BE 里**有两个地方**需要看到明文 ——
 *    1) 分路器/读取器拿数据的地方（CAsyncFileReader::SyncRead，见 AsyncReader.cpp）
 *    2) 「按文件签名选择源过滤器」的地方（CFGManager::CheckBytes，见 FGManager.cpp）
 *       它是自己 CreateFileW + ReadFile 读文件的，完全绕过 1)
 *  两处必须共用同一套实现，否则 2) 嗅探到密文会导致选中错误的分路器。
 *
 *  密钥默认值编译在下面，可用 exe 同目录的 LZ01.ini 覆盖（换密钥免重编译）：
 *      [LZ01]                        （注意：ini 必须 CRLF 换行，Notepad 保存的即可）
 *      key=d5cb...0101               ; 64 个十六进制字符 = 32 字节
 *      nonce=dafad2d4f1a5af22        ; 16 个十六进制字符 = 8 字节
 *      force=0                       ; 1 = 对「没有标记」的文件也按加密处理
 *      n=4194304                     ; force=1 时使用的加密长度
 * ============================================================================
 */

#pragma once

#include <cstdint>
#include <cstdarg>
#include <cstring>

/* ================= LZ01 begin ================= */

#define LZ01_MAGIC          "LZ01"
#define LZ01_TRAILER_SIZE   16

#define LZ01_DEFAULT_KEY    "d5cb3a051f8ec421bcead87822caee434779b7cb1a2ee8ba08ed0185ba43c101"
#define LZ01_DEFAULT_NONCE  "dafad2d4f1a5af22"

typedef struct {
	uint8_t sbox[256];
	uint8_t rk[240];        /* AES-256：15 组轮密钥 × 16 字节 */
} lz01_aes256_t;

typedef struct {
	bool     active;        /* 是否命中 LZ01 容器 */
	uint64_t encLen;        /* 被加密的头部字节数 */
	uint64_t phys;          /* 物理文件大小 */
	uint64_t logical;       /* 逻辑文件大小 = 物理 - 16 */
} lz01_info_t;

/* ---- 全局状态（每个 TU 一份，互不影响） ---- */
static lz01_aes256_t g_lz01_aes;
static uint8_t       g_lz01_nonce[8];
static bool          g_lz01_aesReady = false;
static bool          g_lz01_force    = false;
static uint64_t      g_lz01_forceN   = 0;

/* GF(2^8) 乘法，模 x^8+x^4+x^3+x+1 (0x11b) */
static uint8_t lz01_gmul(uint8_t a, uint8_t b)
{
	uint8_t p = 0;
	for (int i = 0; i < 8; i++) {
		if (b & 1) {
			p ^= a;
		}
		uint8_t hi = a & 0x80;
		a <<= 1;
		if (hi) {
			a ^= 0x1b;
		}
		b >>= 1;
	}
	return p;
}

static uint8_t lz01_gpow(uint8_t a, unsigned n)
{
	uint8_t r = 1;
	while (n) {
		if (n & 1) {
			r = lz01_gmul(r, a);
		}
		a = lz01_gmul(a, a);
		n >>= 1;
	}
	return r;
}

static uint8_t lz01_rotl8(uint8_t x, unsigned n)
{
	return (uint8_t)((x << n) | (x >> (8 - n)));
}

/* S(x) = x^-1 的仿射变换 */
static void lz01_aes256_init(lz01_aes256_t* a, const uint8_t key[32])
{
	for (unsigned i = 0; i < 256; i++) {
		uint8_t inv = (i == 0) ? 0 : lz01_gpow((uint8_t)i, 254);
		a->sbox[i] = (uint8_t)(inv ^ lz01_rotl8(inv, 1) ^ lz01_rotl8(inv, 2)
		                       ^ lz01_rotl8(inv, 3) ^ lz01_rotl8(inv, 4) ^ 0x63);
	}

	memcpy(a->rk, key, 32);
	uint8_t rcon = 1;
	for (int i = 8; i < 60; i++) {
		uint8_t t[4];
		memcpy(t, a->rk + 4 * (i - 1), 4);
		if ((i & 7) == 0) {
			uint8_t tmp = t[0];
			t[0] = (uint8_t)(a->sbox[t[1]] ^ rcon);
			t[1] = a->sbox[t[2]];
			t[2] = a->sbox[t[3]];
			t[3] = a->sbox[tmp];
			rcon = lz01_gmul(rcon, 2);
		} else if ((i & 7) == 4) {
			for (int j = 0; j < 4; j++) {
				t[j] = a->sbox[t[j]];
			}
		}
		for (int j = 0; j < 4; j++) {
			a->rk[4 * i + j] = (uint8_t)(a->rk[4 * (i - 8) + j] ^ t[j]);
		}
	}
}

static void lz01_shiftrows(uint8_t s[16])
{
	uint8_t t;
	t = s[1];  s[1]  = s[5];  s[5]  = s[9];  s[9]  = s[13]; s[13] = t;
	t = s[2];  s[2]  = s[10]; s[10] = t;
	t = s[6];  s[6]  = s[14]; s[14] = t;
	t = s[15]; s[15] = s[11]; s[11] = s[7];  s[7]  = s[3];  s[3]  = t;
}

static void lz01_mixcolumns(uint8_t s[16])
{
	for (int c = 0; c < 4; c++) {
		uint8_t* p = s + 4 * c;
		uint8_t a0 = p[0], a1 = p[1], a2 = p[2], a3 = p[3];
		uint8_t t = a0 ^ a1 ^ a2 ^ a3;
		p[0] = (uint8_t)(a0 ^ t ^ lz01_gmul((uint8_t)(a0 ^ a1), 2));
		p[1] = (uint8_t)(a1 ^ t ^ lz01_gmul((uint8_t)(a1 ^ a2), 2));
		p[2] = (uint8_t)(a2 ^ t ^ lz01_gmul((uint8_t)(a2 ^ a3), 2));
		p[3] = (uint8_t)(a3 ^ t ^ lz01_gmul((uint8_t)(a3 ^ a0), 2));
	}
}

static void lz01_encrypt_block(const lz01_aes256_t* a, const uint8_t in[16], uint8_t out[16])
{
	uint8_t s[16];

	memcpy(s, in, 16);
	for (int i = 0; i < 16; i++) {
		s[i] ^= a->rk[i];
	}

	for (int r = 1; r <= 14; r++) {
		for (int i = 0; i < 16; i++) {
			s[i] = a->sbox[s[i]];
		}
		lz01_shiftrows(s);
		if (r != 14) {
			lz01_mixcolumns(s);
		}
		for (int i = 0; i < 16; i++) {
			s[i] ^= a->rk[16 * r + i];
		}
	}
	memcpy(out, s, 16);
}

/* 计数器块 = nonce(8B) || 大端 64 位块序号 */
static void lz01_keystream(const lz01_aes256_t* a, const uint8_t nonce[8], uint64_t block, uint8_t ks[16])
{
	uint8_t ctr[16];

	memcpy(ctr, nonce, 8);
	for (int i = 0; i < 8; i++) {
		ctr[8 + i] = (uint8_t)(block >> (56 - 8 * i));
	}
	lz01_encrypt_block(a, ctr, ks);
}

static uint64_t lz01_get_be64(const uint8_t* p)
{
	uint64_t v = 0;
	for (int i = 0; i < 8; i++) {
		v = (v << 8) | p[i];
	}
	return v;
}

static uint32_t lz01_get_be32(const uint8_t* p)
{
	return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) | ((uint32_t)p[2] << 8) | (uint32_t)p[3];
}

static int lz01_hexval(char c)
{
	if (c >= '0' && c <= '9') return c - '0';
	if (c >= 'a' && c <= 'f') return c - 'a' + 10;
	if (c >= 'A' && c <= 'F') return c - 'A' + 10;
	return -1;
}

static int lz01_hex2bin(const char* hex, uint8_t* out, size_t outlen)
{
	if (hex == nullptr || strlen(hex) != outlen * 2) {
		return -1;
	}
	for (size_t i = 0; i < outlen; i++) {
		int hi = lz01_hexval(hex[2 * i]);
		int lo = lz01_hexval(hex[2 * i + 1]);
		if (hi < 0 || lo < 0) {
			return -1;
		}
		out[i] = (uint8_t)((hi << 4) | lo);
	}
	return 0;
}

/* 拼接 <dir> 与文件名 */
static void lz01_mkpath(const wchar_t* dir, const wchar_t* name, wchar_t* out, size_t cch)
{
	size_t k = 0;
	for (; dir[k] && k + 1 < cch; k++) {
		out[k] = dir[k];
	}
	for (size_t j = 0; name[j] && k + 1 < cch; j++) {
		out[k++] = name[j];
	}
	out[k] = 0;
}

/* 取 exe 所在目录（含结尾反斜杠） */
static bool lz01_exe_dir(wchar_t* dir, size_t cch)
{
	dir[0] = 0;
	if (GetModuleFileNameW(nullptr, dir, (DWORD)cch) == 0) {
		return false;
	}
	wchar_t* slash = wcsrchr(dir, L'\\');
	if (!slash) {
		return false;
	}
	*(slash + 1) = 0;
	return true;
}

/*
 * 可选调试日志：只有 exe 同目录存在 LZ01_debug.on 时才写 LZ01_debug.log。
 * 平时（没有那个标记文件）几乎零开销。
 */
static void lz01_dbg(const wchar_t* fmt, ...)
{
	static bool init = false;
	static bool on = false;
	static wchar_t logpath[MAX_PATH] = {};

	if (!init) {
		init = true;
		wchar_t dir[MAX_PATH] = {};
		if (lz01_exe_dir(dir, MAX_PATH)) {
			wchar_t onpath[MAX_PATH] = {};
			lz01_mkpath(dir, L"LZ01_debug.on", onpath, MAX_PATH);
			on = (GetFileAttributesW(onpath) != INVALID_FILE_ATTRIBUTES);
			lz01_mkpath(dir, L"LZ01_debug.log", logpath, MAX_PATH);
		}
	}
	if (!on) {
		return;
	}

	wchar_t buf[1024];
	va_list ap;
	va_start(ap, fmt);
	int n = vswprintf(buf, 1024, fmt, ap);
	va_end(ap);
	if (n <= 0) {
		return;
	}
	if (n > 1022) {
		n = 1022;
	}
	buf[n] = L'\n';
	buf[n + 1] = 0;

	HANDLE h = CreateFileW(logpath, FILE_APPEND_DATA,
	                       FILE_SHARE_READ | FILE_SHARE_WRITE, nullptr,
	                       OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, nullptr);
	if (h == INVALID_HANDLE_VALUE) {
		return;
	}
	DWORD wr = 0;
	WriteFile(h, buf, (DWORD)((n + 1) * sizeof(wchar_t)), &wr, nullptr);
	CloseHandle(h);
}

/* 读 exe 同目录的 LZ01.ini（不存在则一律用编译期默认值） */
static void lz01_load_cfg(void)
{
	if (g_lz01_aesReady) {
		return;
	}

	uint8_t key[32];
	lz01_hex2bin(LZ01_DEFAULT_KEY, key, sizeof(key));
	lz01_hex2bin(LZ01_DEFAULT_NONCE, g_lz01_nonce, sizeof(g_lz01_nonce));

	wchar_t dir[MAX_PATH] = {};
	if (lz01_exe_dir(dir, MAX_PATH)) {
		wchar_t ini[MAX_PATH] = {};
		lz01_mkpath(dir, L"LZ01.ini", ini, MAX_PATH);

		char hex[128] = {};
		wchar_t wbuf[128];

		if (GetPrivateProfileStringW(L"LZ01", L"key", L"", wbuf, 128, ini) > 0) {
			for (int i = 0; wbuf[i] && i < 127; i++) {
				hex[i] = (char)wbuf[i];
			}
			uint8_t tmp[32];
			if (lz01_hex2bin(hex, tmp, sizeof(tmp)) == 0) {
				memcpy(key, tmp, sizeof(tmp));
			}
		}

		memset(hex, 0, sizeof(hex));
		if (GetPrivateProfileStringW(L"LZ01", L"nonce", L"", wbuf, 128, ini) > 0) {
			for (int i = 0; wbuf[i] && i < 127; i++) {
				hex[i] = (char)wbuf[i];
			}
			uint8_t tmp[8];
			if (lz01_hex2bin(hex, tmp, sizeof(tmp)) == 0) {
				memcpy(g_lz01_nonce, tmp, sizeof(tmp));
			}
		}

		g_lz01_force = (GetPrivateProfileIntW(L"LZ01", L"force", 0, ini) != 0);
		if (g_lz01_force) {
			wchar_t nbuf[64] = {};
			if (GetPrivateProfileStringW(L"LZ01", L"n", L"0", nbuf, 64, ini) > 0) {
				g_lz01_forceN = wcstoull(nbuf, nullptr, 10);
			}
		}
	}

	lz01_aes256_init(&g_lz01_aes, key);
	g_lz01_aesReady = true;

	{
		uint8_t ks[16];
		lz01_keystream(&g_lz01_aes, g_lz01_nonce, 0, ks);
		lz01_dbg(L"[cfg] ready=%d force=%d n=%I64u nonce0=%02x%02x%02x%02x ks0=%02x%02x%02x%02x",
		         (int)g_lz01_aesReady, (int)g_lz01_force, g_lz01_forceN,
		         g_lz01_nonce[0], g_lz01_nonce[1], g_lz01_nonce[2], g_lz01_nonce[3],
		         ks[0], ks[1], ks[2], ks[3]);
	}
}

/* 就地解密 buf 中落在 [0, encLen) 内的部分；off 为该缓冲区在文件中的绝对偏移 */
static void lz01_decrypt_inplace(void* buf, size_t len, uint64_t off, uint64_t encLen)
{
	if (encLen == 0 || off >= encLen) {
		return;
	}

	size_t n = len;
	if (off + n > encLen) {
		n = (size_t)(encLen - off);
	}

	uint8_t* p = (uint8_t*)buf;
	uint64_t blk = off >> 4;
	size_t skip = (size_t)(off & 15);
	size_t i = 0;

	while (i < n) {
		uint8_t ks[16];
		lz01_keystream(&g_lz01_aes, g_lz01_nonce, blk, ks);

		size_t take = 16 - skip;
		if (take > n - i) {
			take = n - i;
		}
		for (size_t j = 0; j < take; j++) {
			p[i + j] ^= ks[skip + j];
		}

		i += take;
		skip = 0;
		blk++;
	}
}

/* 单个字节的解密（供「逐字节嗅探签名」用） */
static uint8_t lz01_decrypt_byte(uint8_t b, uint64_t off, uint64_t encLen)
{
	if (encLen == 0 || off >= encLen) {
		return b;
	}
	uint8_t ks[16];
	lz01_keystream(&g_lz01_aes, g_lz01_nonce, off >> 4, ks);
	return (uint8_t)(b ^ ks[off & 15]);
}

/* 在已打开的文件句柄上探测末尾标记；不改变文件的最终读指针（会恢复） */
static bool lz01_probe_handle(HANDLE hFile, lz01_info_t* out)
{
	if (out) {
		memset(out, 0, sizeof(*out));
	}
	if (hFile == INVALID_HANDLE_VALUE || !out) {
		return false;
	}

	LARGE_INTEGER sz = {};
	if (!GetFileSizeEx(hFile, &sz) || sz.QuadPart <= LZ01_TRAILER_SIZE) {
		return false;
	}
	out->phys = (ULONGLONG)sz.QuadPart;

	lz01_load_cfg();

	LARGE_INTEGER zero = {}, saved = {};
	SetFilePointerEx(hFile, zero, &saved, FILE_CURRENT);

	const ULONGLONG end = out->phys - LZ01_TRAILER_SIZE;
	uint8_t tail[LZ01_TRAILER_SIZE] = {};

	LARGE_INTEGER off = {};
	off.QuadPart = (LONGLONG)end;
	BOOL okSeek = SetFilePointerEx(hFile, off, nullptr, FILE_BEGIN);
	DWORD rd = 0;
	BOOL okRead = okSeek ? ReadFile(hFile, tail, LZ01_TRAILER_SIZE, &rd, nullptr) : FALSE;

	SetFilePointerEx(hFile, saved, nullptr, FILE_BEGIN);

	if (!okRead || rd != LZ01_TRAILER_SIZE || memcmp(tail, LZ01_MAGIC, 4) != 0) {
		/* 没有标记时，考虑 force 模式（比如尾部标记被裁掉的变体） */
		if (g_lz01_force && g_lz01_forceN > 0) {
			out->active = true;
			out->logical = out->phys;
			out->encLen = (g_lz01_forceN <= out->phys) ? g_lz01_forceN : out->phys;
		}
		return out->active;
	}

	const uint32_t version = lz01_get_be32(tail + 4);
	const uint64_t encLen = lz01_get_be64(tail + 8);

	if (version == 1 && encLen > 0 && encLen <= end) {
		out->active = true;
		out->encLen = encLen;
		out->logical = end;
		return true;
	}
	return false;
}

/* ================== LZ01 end ================== */
