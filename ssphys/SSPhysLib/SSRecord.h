// SSRecord.h: interface for the SSRecord class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_SSRECORD_H__2A40F202_FFA7_401B_87D7_FDA36EF531B9__INCLUDED_)
#define AFX_SSRECORD_H__2A40F202_FFA7_401B_87D7_FDA36EF531B9__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000


#include "SSTypes.h"
#include "SSFiles.h"

//---------------------------------------------------------------------------
enum eType {
  eNone,
  eItemRecord,      // DH, DH_PROJECT, DH_FILE
  eHistoryRecord,   // EL
  eCommentRecord,   // MC
  eCheckOutRecord,  // CF
  eParentFolder,    // PF
  eFileDelta,       // FD
  eNamesCache,      // HN
  eNameCacheEntry,  // SN
  eProjectEntry,    // JP
  eUsersHeader,     // HU
  eUser,            // UU
  eBranchFile,      // BF
  eUnknown
};

class SSRecord
{
  friend class SSFileImp;
  SSRecord (SSFileImpPtr filePtr, off_t offset);

public:
  SSRecord (eType type, const void* buffer, off_t len);
  ~SSRecord ();

  static eType        StringToType  (const char type[2]);
  static std::string  TypeToString  (eType type);
  
  bool IsValid () const;

  const byte* GetBuffer () const { return m_pBuffer; }
  byte* GetBuffer ()             { return m_pBuffer; }
  off_t GetLen ()            const { return m_Len; }
  off_t GetOffset ()        const { return m_Offset; }
  off_t GetNextOffset ()    const { return m_Offset + m_Len + sizeof(m_Header); }
  std::string GetRecordType () const { return std::string (m_Header.type, 2); }
  eType GetType () const;

  SSFileImpPtr GetFileImp () const { return m_FileImpPtr; }

  void Dump (std::ostream& os) const;
  
private:
  RECORD_HEADER m_Header;
  byte* m_pBuffer;
  off_t m_Len;
  off_t m_Offset;
  SSFileImpPtr m_FileImpPtr;
};

typedef boost::shared_ptr<SSRecord> SSRecordPtr;


#endif // !defined(AFX_SSRECORD_H__2A40F202_FFA7_401B_87D7_FDA36EF531B9__INCLUDED_)
