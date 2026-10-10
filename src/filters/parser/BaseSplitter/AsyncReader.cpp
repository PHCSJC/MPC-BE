/*
 * (C) 2003-2006 Gabest
 * (C) 2006-2024 see Authors.txt
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
 *  本地补丁：LZ01 加密容器支持
 *
 *  容器格式：  [前 N 字节 AES-256-CTR 密文][其余明文][末尾 16 字节标记]
 *  末尾标记：  "LZ01" | version(u32 大端) | N(u64 大端)        共 16 字节
 *  CTR 计数器块 = nonce(8B) || 大端 64 位块序号(8B)，从 0 开始计数。
 *
 *  CTR 可随机寻址，因此本补丁在「异步读取器」这一层做就地解密：
 *    Open()     探测末尾 16 字节；命中则记录 N，并把对外长度改为 物理-16
 *    SyncRead() 读完之后，只对落在 [0, N) 区间内的部分做 XOR 解密
 *  全程不产生任何解密中间文件，也不改分流器 / 解码器。
 *
 *  密钥默认值编译在下面，可用 exe 同目录的 LZ01.ini 覆盖（换密钥免重编译）：
 *      [LZ01]
 *      key=d5cb...0101          ; 64 个十六进制字符 = 32 字节
 *      nonce=dafad2d4f1a5af22   ; 16 个十六进制字符 = 8 字节
 *      force=0                  ; 1 = 对「没有标记」的文件也按加密处理
 *      n=4194304                ; force=1 时使用的加密长度
 *
 *  AES 实现刻意内联在本文件内（不改任何工程/构建文件），
 *  且 S-box 由 GF(2^8) 运算现场生成，避免手抄 256 字节表出错。
 * ============================================================================
 */

#include "stdafx.h"
#include "AsyncReader.h"
#include "DSUtil/UrlParser.h"
#include "DSUtil/Log.h"

#include <cstdint>
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
	if (GetModuleFileNameW(nullptr, dir, MAX_PATH) != 0) {
		wchar_t* slash = wcsrchr(dir, L'\\');
		if (slash) {
			*(slash + 1) = 0;
		}
		/* 拼出 <exe目录>\LZ01.ini（手写拼接，避免依赖 _s 系列函数） */
		wchar_t ini[MAX_PATH] = {};
		int k = 0;
		for (; dir[k] && k < MAX_PATH - 12; k++) {
			ini[k] = dir[k];
		}
		const wchar_t* tail = L"LZ01.ini";
		for (int j = 0; tail[j] && k < MAX_PATH - 1; j++, k++) {
			ini[k] = tail[j];
		}
		ini[k] = 0;

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

/* ================== LZ01 end ================== */

//
// CAsyncFileReader
//

CAsyncFileReader::CAsyncFileReader(CString fn, HRESULT& hr, BOOL bSupportURL)
	: CUnknown(L"CAsyncFileReader", nullptr, &hr)
	, m_bSupportURL(bSupportURL)
{
	hr = Open(fn) ? S_OK : E_FAIL;
}

CAsyncFileReader::CAsyncFileReader(CHdmvClipInfo::CPlaylist& Items, HRESULT& hr)
	: CUnknown(L"CAsyncFileReader", nullptr, &hr)
{
	hr = OpenFiles(Items) ? S_OK : E_FAIL;
}

STDMETHODIMP CAsyncFileReader::NonDelegatingQueryInterface(REFIID riid, void** ppv)
{
	CheckPointer(ppv, E_POINTER);

	return
		QI(IAsyncReader)
		QI(ISyncReader)
		QI(IFileHandle)
		__super::NonDelegatingQueryInterface(riid, ppv);
}

BOOL CAsyncFileReader::Open(LPCWSTR lpszFileName)
{
	if (::PathIsURLW(lpszFileName)) {
		CUrlParser urlParser;
		if (m_bSupportURL
				&& urlParser.Parse(lpszFileName)
				&& m_HTTPAsync.Connect(lpszFileName, http::connectTimeout) == S_OK) {
			const UINT64 ContentLength = m_HTTPAsync.GetLenght();
			if (ContentLength == 0) {
				return FALSE;
			}

			m_total = ContentLength;
			m_url = lpszFileName;
			m_sourcetype = SourceType::HTTP;

			return TRUE;
		}

		return FALSE;
	}

	if (!__super::Open(lpszFileName)) {
		return FALSE;
	}

	/* ---------- 本地补丁：LZ01 探测 ---------- */
	m_lz01_encLen = 0;
	m_lz01_phys   = __super::GetLength();

	lz01_load_cfg();

	if (m_lz01_phys > LZ01_TRAILER_SIZE) {
		const ULONGLONG end = m_lz01_phys - LZ01_TRAILER_SIZE;

		uint8_t tail[LZ01_TRAILER_SIZE] = {};
		if (Seek((LONGLONG)end, FILE_BEGIN) == end) {
			DWORD dwError = ERROR_SUCCESS;
			if (Read(tail, LZ01_TRAILER_SIZE, dwError) == LZ01_TRAILER_SIZE
					&& memcmp(tail, LZ01_MAGIC, 4) == 0) {
				const uint32_t version = lz01_get_be32(tail + 4);
				const uint64_t encLen  = lz01_get_be64(tail + 8);

				if (version == 1 && encLen > 0 && encLen <= end) {
					m_lz01_encLen = encLen;
					m_total       = end;        // 对外长度 = 物理长度 - 16
					DLog(L"CAsyncFileReader::Open() : LZ01 container, encrypt header %I64u bytes, logical size %I64u", encLen, end);
				} else {
					DLog(L"CAsyncFileReader::Open() : LZ01 marker found but version/N invalid (v=%u N=%I64u) - ignored", version, encLen);
				}
			}
		}
		Seek(0, FILE_BEGIN);
	}

	/* force=1 时，对「没有标记」的文件也按加密处理（例如尾部标记被裁掉的变体） */
	if (m_lz01_encLen == 0 && g_lz01_force && g_lz01_forceN > 0) {
		const uint64_t logical = (uint64_t)m_lz01_phys;
		m_lz01_encLen = (g_lz01_forceN <= logical) ? g_lz01_forceN : logical;
		m_total       = logical;
		DLog(L"CAsyncFileReader::Open() : LZ01 forced mode, encrypt header %I64u bytes", m_lz01_encLen);
	}
	/* ---------- 补丁结束 ---------- */

	return TRUE;
}

ULONGLONG CAsyncFileReader::GetLength()
{
	return m_total ? m_total : __super::GetLength();
}

// IAsyncReader

STDMETHODIMP CAsyncFileReader::SyncRead(LONGLONG llPosition, LONG lLength, BYTE* pBuffer)
{
	if ((ULONGLONG)llPosition + lLength > GetLength()) {
		return E_FAIL;
	}

	if (m_url.GetLength()) {
		auto RetryOnError = [&] {
			const DWORD dwError = GetLastError();
			if (dwError == ERROR_INTERNET_CONNECTION_RESET
					|| dwError == ERROR_HTTP_INVALID_SERVER_RESPONSE) {
				if (S_OK == m_HTTPAsync.Seek(llPosition)) {
					return true;
				}
			}
			return false;
		};

		for (;;) {
			if (m_pos != llPosition) {
				if (llPosition > m_pos && (llPosition - m_pos) <= 64 * KILOBYTE) {
					static std::vector<BYTE> pBufferTmp(64 * KILOBYTE);
					const DWORD lenght = llPosition - m_pos;

					DWORD dwSizeRead = 0;
					HRESULT hr = m_HTTPAsync.Read(pBufferTmp.data(), lenght, dwSizeRead, http::readTimeout);
					if (hr != S_OK || dwSizeRead != lenght) {
						if (RetryOnError()) {
							continue;
						}
						return E_FAIL;
					}
				} else {
					HRESULT hr = m_HTTPAsync.Seek(llPosition);
#ifdef DEBUG_OR_LOG
					DLog(L"CAsyncFileReader::SyncRead() : do HTTP seeking from %I64d to %I64d, hr = 0x%08x", m_pos, llPosition, hr);
#endif
					if (hr != S_OK) {
						return hr;
					}
				}

				m_pos = llPosition;
			}

			DWORD dwSizeRead = 0;
			HRESULT hr = m_HTTPAsync.Read(pBuffer, lLength, dwSizeRead, http::readTimeout);
			if (hr != S_OK || dwSizeRead != lLength) {
				if (RetryOnError()) {
					continue;
				}
				return E_FAIL;
			}
			m_pos += dwSizeRead;

			return S_OK;
		}

		return E_FAIL;
	}

	try {
		if ((ULONGLONG)llPosition != Seek(llPosition, FILE_BEGIN)) {
			return E_FAIL;
		}
		DWORD dwError;
		UINT readed = Read(pBuffer, lLength, dwError);
		if (readed < (UINT)lLength || dwError != ERROR_SUCCESS) {
			return E_FAIL;
		}

		/* ---------- 本地补丁：就地解密 ---------- */
		if (m_lz01_encLen != 0) {
			lz01_decrypt_inplace(pBuffer, (size_t)lLength, (uint64_t)llPosition, m_lz01_encLen);
		}
		/* ---------- 补丁结束 ---------- */

		return S_OK;
	}
	catch (CFileException* e) {
		m_lOsError = e->m_lOsError;
		e->Delete();

		return E_FAIL;
	}
}

STDMETHODIMP CAsyncFileReader::Length(LONGLONG* pTotal, LONGLONG* pAvailable)
{
	const LONGLONG len = GetLength();

	if (pTotal) {
		*pTotal = len;
	}
	if (pAvailable) {
		*pAvailable = len;
	}
	return S_OK;
}
