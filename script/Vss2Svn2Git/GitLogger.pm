package Vss2Svn2Git::GitLogger;

use Git::Repository::Plugin;
use Git::Repository::Command;
our @ISA = qw( Git::Repository::Plugin );

sub _keywords { return qw( logrun setlog ) }

sub setlog {
    my ($r, $val) = @_;

    $r->{'_plugin_gitlogger_log'} = $val;
}

sub logrun {
    my ($r,@cmd) = @_;

    # This code basically that of Git::Repository run()

    # split the args to get the optional callbacks
    my @cb;
    @cmd = grep { ref eq 'CODE' ? !push @cb, $_ : 1 } @cmd;

    local $Carp::CarpLevel = 1;

    my $command = Git::Repository::Command->new($r, @cmd);

    if (defined $r->{'_plugin_gitlogger_log'}
        && $r->{'_plugin_gitlogger_log'}) {
        print "git cmd:";
        print join q{ }, $command->cmdline();
        print "\n";
    }

    # return the output or die
    return $command->final_output(@cb);

}

1;
