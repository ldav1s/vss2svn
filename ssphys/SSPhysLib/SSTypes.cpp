// SSTypes.cpp:
//
//////////////////////////////////////////////////////////////////////

#include "StdAfx.h"
#include "SSTypes.h"

//---------------------------------------------------------------------------
const char* const g_szActions[] = {
  "Labeled",            // = 0
  "Created Project",    // = 1
  "Added Project",      // = 2
  "Added File",         // = 3
  "Destroyed Project",  // = 4
  "Destroyed File",     // = 5
  "Deleted Project",    // = 6
  "Deleted File",       // = 7
  "Recovered Project",  // = 8
  "Recovered File",     // = 9
  "Renamed Project",    // = 10
  "Renamed File",       // = 11
  "Moved Project From", // = 12
  "Moved Project To",   // = 13
  "Shared File",        // = 14
  "Branch File",        // = 15
  "Created File",       // = 16
  "Checked In",         // = 17
  "Action 18",          // missing action 18
  "RollBack",           // = 19
  "Archive Versions of File",  // = 20
  "Action 19",          // missing action 19
  "Archive File",      // = 22
  "Archive Project",   // = 23
  "Restored File",      // = 24
  "Restored Project",   // = 25

  /// --- pseudo actions ---
  "Pinned File",        // = 26
  "Unpinned File"       // = 27
};

const char* CAction::ActionToString (eAction e)
{
  if (e < countof (g_szActions))
    return g_szActions[e];
  return ("unknown");
}

