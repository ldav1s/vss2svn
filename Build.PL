use Module::Build;

Module::Build->new
    ( dist_name => 'Vss2Svn',
      dist_version_from => 'script/vss2svn.pl',
      configure_requires => {'Module::Build' => 0.38},
      dist_abstract => 'converts SourceSafe database to subversion repository',
      license => 'gpl',
      requires => {
	  'Getopt::Long' => '>= 2.34',
	  'DBI' => '>= 1.47',
	  'DBD::SQLite' => '>= 1.37',
	  'XML::LibXML' => '>= 2.0019',
	  'Data::UUID' => 0,
	  'File::Find' => 0,
	  'File::Path' => 0,
	  'Git::Repository' => '>= 1.27',
	  'Time::CTime' => 0,
          'Hash::Case' => 0,
          'File::Spec' => 0,
          'IPC::Run' => 0,
          'Data::Dumper' => 0,
      },
      script_files => { 'script/vss2svn.pl' => 'script/vss2svn.pl', 'ssphys/ssphys' => 'bin/ssphys'},
      pm_files => { 'script/Vss2Svn2Git/GitLogger.pm' => 'lib/Vss2Svn2Git/GitLogger.pm' },
      PL_files => { 'ssphys/ssphys.PL' => 'bin/ssphys' },
      )->create_build_script;
