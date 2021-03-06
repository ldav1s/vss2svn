// ValidateCommand.cpp: implementation of the ValidateCommand class.
//
//////////////////////////////////////////////////////////////////////

#include "StdAfx.h"
#include "ValidateCommand.h"
#include <SSPhysLib/SSFiles.h>
//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

//---------------------------------------------------------------------------
CValidateCommand::CValidateCommand ()
  : CMultiArgCommand ("validate", "Validates the condition of a VSS physical file")
{
}


void CValidateCommand::Execute (po::variables_map const& options, std::string const& arg)
{
  std::auto_ptr<SSRecordFile> pFile (SSRecordFile::MakeFile (arg));
  if (pFile.get())
  {
    pFile->Validate ();
  }
}
