package Vss2Svn::SvnRevHandler;

use warnings;
use strict;

our(%gCfg);

$gCfg{revtimerange} = 3600;

###############################################################################
#  new
###############################################################################
sub new {
    my($class) = @_;

    my $svncache = Vss2Svn::DataCache->new('SvnRevision', 1);
  
    # we need to start at revision 1 and not 0
    ++$svncache->{pkey};
  
    if (!defined($svncache)) {
        print "\nERROR: Could not create cache 'SvnRevision'\n";
        return undef;
    }

    my $self =
        {
         svncache => $svncache,
         revnum => undef,
        };

    $self = bless($self, $class);

    $self->_init();
    return $self;

}  #  End new

###############################################################################
#  _init
###############################################################################
sub _init {
    my($self) = @_;

    $self->{timestamp} = undef;
    $self->{author} = undef;
    $self->{comment} = undef;
    $self->{lastcommentaction} = undef;
    $self->{seen} = {};
    $self->{last_action} = {};
    $self->{abs_last_action} = undef;

}  #  End _init

###############################################################################
#  check
###############################################################################
sub check {
    my($self, $data) = @_;

    my($physname, $itemtype, $actiontype, $timestamp, $author, $comment) =
        @{ $data }{qw( physname itemtype actiontype timestamp author comment )};
    my($prevtimestamp, $prevauthor, $prevcomment, $prevaction) =
        @{ $self }{qw( timestamp author comment actiontype)};

    # Any of the following cause a new SVN revision:
    #   * same file touched more than once
    #   * different author
    #   * different comment
    #   * time range exceeds threshold num. of seconds (default 3600)
    #   * any action on a directory other than add

    my $wasseen = $self->{seen}->{$physname};
    my $last_action = $self->{last_action}->{$physname};
    my $abs_last_action = $self->{abs_last_action};

    # in case the current action is the same as the last action
    if ($actiontype eq 'SHARE' && $wasseen && $last_action eq $actiontype) {
        $wasseen = 0;
    }
    
    # if an add is followed by a share we omit the check for the comment. In most
    # cases this is a bulk share started with a project. But the comment is
    # only recorded for the project ADDs and not for the files SHARES
    if ($actiontype eq 'SHARE' && !defined $comment
        && defined $self->{lastcommentaction}
        && $self->{lastcommentaction} eq 'ADD') {
        $comment = $prevcomment;
    }
    else {
        $self->{lastcommentaction} = $actiontype;
    }

    # Destroyed files have the undef comment.
    # We should check to make sure if this is the case.
    if (!defined $comment) {
        # toss out the offending comment
        $comment = $prevcomment;
    }

    # Isolate labels from other actions
    if (defined $abs_last_action
        && $abs_last_action eq 'LABEL'
        && $actiontype ne 'LABEL') {
        $self->{commitPending} = 1;
    }

    no warnings 'uninitialized';
    if($wasseen
       || (lc $author ne lc $prevauthor)
       || ($timestamp - $prevtimestamp > $gCfg{revtimerange})
       || ($comment ne $prevcomment)
       || ($itemtype == 1 && $actiontype ne 'ADD')
       || $self->{commitPending} ) {

        $self->new_revision($data);

        if ($self->{verbose}) {
            print "\n**** NEW SVN REVISION ($self->{revnum}): ",
            join(',', $physname, $timestamp, $author, $comment), "\n";
        }
    }
    
    # Any of the following actions needs to be commited the next time:
    #  * any action on a directory other than add
    #  * the first initial creation of the $/ project
    $self->{commitPending} = ($itemtype == 1 && $actiontype ne 'ADD') || ($self->{revnum} == 0);
    
    $self->{seen}->{$physname}++;
    $self->{last_action}->{$physname} = $actiontype;
    $self->{abs_last_action} = $actiontype;

    @{ $self }{qw( timestamp author comment actiontype)} =
        ($timestamp, $author, $comment, $actiontype);

}  #  End check

###############################################################################
#  new_revision
###############################################################################
sub new_revision {
    my($self, $data) = @_;

    $self->{svncache}->add( @{ $data }{qw(timestamp author comment)} );
    $self->{revnum} = $self->{svncache}->{pkey};
    $self->{seen} = {};
    $self->{last_action} = {};
    $self->{commitPending} = undef;
    $self->{abs_last_action} = undef;

}  #  End new_revision

###############################################################################
#  commit
###############################################################################
sub commit {
    my($self) = @_;

    $self->{svncache}->commit();
}  #  End commit

###############################################################################
#  SetRevTimeRange
###############################################################################
sub SetRevTimeRange {
    my($class, $range) = @_;

    $gCfg{revtimerange} = $range;
}  #  End SetRevTimeRange


1;
