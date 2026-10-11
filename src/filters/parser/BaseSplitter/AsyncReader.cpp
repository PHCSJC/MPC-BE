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
 *  本地补丁：LZ01 加密容器支持（读取器一侧）
 *
 *  在「异步读取器」这一层做就地解密：
 *    GetLength() 懒触发 LZ01_Probe() —— 命中则把对外长度改为「物理 - 16」
 *    SyncRead()  读完之后，只对落在 [0, N) 区间内的部分做 XOR 解密
 *  全程不产生解密中间文件，也不改分流器 / 解码器。
 *
 *  注意：探测刻意做成「懒加载」而不是只在 Open() 里做 —— 因为 MPC-BE 打开
 *  本地文件有两条构造路径：
 *      CAsyncFileReader(pszFileName, hr, ...)  → Open()
 *      CAsyncFileReader(m_Items, hr)           → OpenFiles()
 *  而 GetLength() 两条路径都会被调用，放在这里才覆盖得全。
 *
 *  加密算法与标记解析都在 DSUtil/LZ01.h（header-only），
 *  与 FGManager.cpp 的「签名嗅探」共用同一份实现。
 * ============================================================================
 */

#include "stdafx.h"
#include "AsyncReader.h"
#include "DSUtil/UrlParser.h"
#include "DSUtil/Log.h"
#include "DSUtil/LZ01.h"

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

/* ---------- 本地补丁：LZ01 探测（懒加载，两条构造路径都覆盖） ---------- */
void CAsyncFileReader::LZ01_Probe()
{
	if (m_lz01Checked) {
		return;
	}
	m_lz01Checked = true;
	m_lz01_encLen = 0;

	lz01_dbg(L"[probe] enter: sourcetype=%d url=%d hFile=%d parts=%zu",
	         (int)m_sourcetype, (int)(m_url.IsEmpty() ? 0 : 1),
	         (int)(m_hFile != INVALID_HANDLE_VALUE), (size_t)m_strFiles.size());

	/* 只处理本地单文件；网络源与蓝光多文件播放列表不处理 */
	if (m_sourcetype != SourceType::LOCAL || !m_url.IsEmpty()
			|| m_hFile == INVALID_HANDLE_VALUE || m_strFiles.size() != 1) {
		return;
	}

	lz01_info_t info;
	if (!lz01_probe_handle(m_hFile, &info) || !info.active) {
		return;
	}

	m_lz01_phys   = info.phys;
	m_lz01_encLen = info.encLen;
	m_total       = info.logical;      // 对外长度 = 物理长度 - 16

	lz01_dbg(L"[probe] ACCEPTED encLen=%I64u logical=%I64u phys=%I64u",
	         m_lz01_encLen, (unsigned long long)m_total, m_lz01_phys);
	DLog(L"CAsyncFileReader : LZ01 container, encrypt header %I64u bytes, logical size %I64u",
	     m_lz01_encLen, (unsigned long long)m_total);
}
/* ---------- 补丁结束 ---------- */

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

	LZ01_Probe();      // 本地补丁

	return TRUE;
}

ULONGLONG CAsyncFileReader::GetLength()
{
	LZ01_Probe();      // 本地补丁：懒探测（单文件构造 / 播放列表构造都会到这里）
	return m_total ? m_total : __super::GetLength();
}

// IAsyncReader

STDMETHODIMP CAsyncFileReader::SyncRead(LONGLONG llPosition, LONG lLength, BYTE* pBuffer)
{
	{
		static volatile LONG s_in_cnt = 0;
		const LONG c = InterlockedIncrement(&s_in_cnt);
		if (c <= 24 || (c % 8192) == 0) {
			lz01_dbg(L"[sync] #%ld pos=%I64d len=%d logical=%I64u encLen=%I64u",
			         c, (__int64)llPosition, (int)lLength,
			         (unsigned long long)GetLength(), (unsigned long long)m_lz01_encLen);
		}
	}

	if ((ULONGLONG)llPosition + lLength > GetLength()) {
		lz01_dbg(L"[sync] *** GUARD REJECT pos=%I64d len=%d logical=%I64u",
		         (__int64)llPosition, (int)lLength, (unsigned long long)GetLength());
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
			static volatile LONG s_dbg_cnt = 0;
			const LONG cnt = InterlockedIncrement(&s_dbg_cnt);
			if (cnt <= 6) {
				lz01_dbg(L"[read] #%ld off=%I64u len=%u encLen=%I64u  BEFORE=%02x%02x%02x%02x",
				         cnt, (unsigned long long)llPosition, (unsigned)lLength,
				         (unsigned long long)m_lz01_encLen,
				         pBuffer[0], pBuffer[1], pBuffer[2], pBuffer[3]);
			}
			lz01_decrypt_inplace(pBuffer, (size_t)lLength, (uint64_t)llPosition, m_lz01_encLen);
			if (cnt <= 6) {
				lz01_dbg(L"[read] #%ld AFTER =%02x%02x%02x%02x  (明文头应为 00000020 66747970)",
				         cnt, pBuffer[0], pBuffer[1], pBuffer[2], pBuffer[3]);
			}
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
