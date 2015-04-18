#!/usr/bin/perl
# irpg bot v3.1.2 by jotun, jotun@idlerpg.net, et al. See http://idlerpg.net/
#
# Some code within this file was written by authors other than myself. As such,
# distributing this code or distributing modified versions of this code is
# strictly prohibited without written authorization from the authors. Contact
# jotun@idlerpg.net. Please note that this may change (at any time, no less) if
# authorization for distribution is given by patch submitters.
#
# As a side note, patches submitted for this project are automatically taken to
# be freely distributable and modifiable for any use, public or private, though
# I make no claim to ownership; original copyrights will be retained.. except as
# I've just stated.
#
# Please mail bugs, etc. to me. Patches are welcome to fix bugs or clean up
# the code, but please do not use a radically different coding style. Thanks
# to everyone that's contributed!
#
# NOTE: This code should NOT be run as root. You deserve anything that happens
#       to you if you run this code as a superuser. Also, note that giving a
#       user admin access to the bot effectively gives them full access to the
#       user under which your bot runs, as they can use the PEVAL command to
#       execute any command, or possibly even change your password. I sincerely
#       suggest that you exercise extreme caution when giving someone admin
#       access to your bot, or that you disable the PEVAL command for non-owner
#       accounts in your config file, .irpg.conf

use strict;
use warnings;
use IO::Socket;
use IO::Select;
use Data::Dumper;
use Getopt::Long;

my $version = "3.1.2_modFP";

my %opts;

my $conffile = '.irpg.conf';
readconfig();

# command line overrides .irpg.conf
GetOptions(\%opts,
    "help|h",
    "verbose|v",
    "debug",
    "debugfile=s",
    "modsfile=s",
    "server|s=s",
    "botnick|n=s",
    "botuser|u=s",
    "botrlnm|r=s",
    "botchan|c=s",
    "botident|p=s",
    "botmodes|m=s",
    "botopcmd|o=s",
    "localaddr=s",
    "botghostcmd|g=s",
    "helpurl=s",
    "admincommurl=s",
    "doban",
    "silentmode=i",
    "questfilename=s",
    "voiceonlogin",
    "noccodes",
    "nononp",
    "mapurl=s",
    "statuscmd",
    "pidfile=s",
    "reconnect",
    "reconnect_wait=i",
    "self_clock=i",
    "casematters",
    "detectsplits",
    "splitwait=i",
    "allowuserinfo",
    "noscale",
    "phonehome",
    "owner=s",
    "owneraddonly",
    "ownerdelonly",
    "ownerpevalonly",
    "checkupdates",
    "senduserlist",
    "limitpen=i",
    "mapx=i",
    "mapy=i",
    "modesperline=i",
    "okurl|k=s@",
    "eventsfile=s",
    "itemsfile=s",
    "rpstep=f",
    "rpbase=i",
    "rppenstep=f",
    "dbfile|irpgdb|db|d=s",
    "itemdbfile|idb=s",
    "daemonize",
    "top_period=i",
    "chal_period",
) or debug("Error: Could not parse command line. Try $0 --help\n",1);

$opts{help} and do { help(); exit 0; };

debug("Config: read $_: ".Dumper($opts{$_})) for keys(%opts);

my @items;
my @levels;
my @calamity;
my @godsend;
my @uniques;
my %uniques; # letter to index mapping
my @fragileitems;
read_items();

my @quests;
my %events;
my %uniquemsg; # indexed by lower case alignment 'g', 'n', 'e'.
read_events();

# Utility variables that lots of parametrised functions can use
# direction of time:
my @tofrom = ('from', 'toward');
# gender: male, female, unknown, neutral, politically correct
my %hesheit = (m => 'he', f => 'she', u => 'they', n => 'it', pc => 'he/she/it');
my %himherit = (m =>'him',f => 'her', u => 'them', n => 'it', pc => 'him/her/it');
my %hisherits = (m=>'his',f => 'her', u => 'their',n => 'its',pc => 'his/her/its');
my %hishersits= (m=>'his',f => 'hers',u =>'theirs',n => 'its',pc => 'his/hers/its');

my %rps; # role-players
sub they( $ ) { return $hesheit{   exists($rps{$_[0]}) ? $rps{$_[0]}{gender} : 'u'}; }
sub them( $ ) { return $himherit{  exists($rps{$_[0]}) ? $rps{$_[0]}{gender} : 'u'}; }
sub their( $ ) { return $hisherits{exists($rps{$_[0]}) ? $rps{$_[0]}{gender} : 'u'}; }

sub are( $ ) { return (!exists($rps{$_[0]}) or $rps{$_[0]}{gender} eq 'u') ? 'are' : 'is'; }
sub were( $ ) { return (!exists($rps{$_[0]}) or $rps{$_[0]}{gender} eq 'u') ? 'were' : 'was'; }
sub have( $ ) { return (!exists($rps{$_[0]}) or $rps{$_[0]}{gender} eq 'u') ? 'have' : 'has'; }
#sub verb( $ ) { return (!exists($rps{$_[0]}) or $rps{$_[0]}{gender} eq 'u') ? '' : 's'; }

my $outbytes = 0; # sent bytes
my $primnick = $opts{botnick}; # for regain or register checks
my $inbytes = 0; # received bytes
my %onchan; # users on game channel
my %quest = restorequest();

my $mapitems_dirty;
my %mapitems = (); # indexed by "$x:$y", each being a list of items

my $rpreport = 0; # constant for reporting top players
my $oldrpreport = 0; # prior $rpreport so threshold-crossing can be detected
sub report_threshold( $ ) { return int($rpreport/$_[0]) > int($oldrpreport/$_[0]); }

my %prev_online; # user@hosts online on restart, die
my %auto_login; # users to automatically log back on
my $pausemode = 0; # pausemode on/off flag
my $silentmode = 0; # silent mode 0/1/2/3, see head of file
my $lastreg = 0; # holds the time of the last reg. cleared every second.
                 # prevents more than one account being registered / second
my $registrations = 0; # count of registrations this period
my $lasttime = 1; # last time that rpcheck() was run

# each of these is server-specific
my @bans; # bans auto-set by the bot, saved to be removed after 1 hour
my @queue; # outgoing message queue
my $sel; # IO::Select object
my $buffer; # buffer for socket stuff
my $conn_tries = 0; # number of connection tries. gives up after trying each
                    # server twice
my $sock; # IO::Socket::INET object
my %split; # holds nick!user@hosts for clients that have been netsplit
my $freemessages = 4; # number of "free" privmsgs we can send. 0..$freemessages

sub daemonize(); # prototype to avoid warnings

if (! -e $opts{dbfile}) {
    $|=1;
    %rps = ();
    print "$opts{dbfile} does not appear to exist. I'm guessing this is your ".
          "first time using IRPG. Please give an account name that you would ".
          "like to have admin access [$opts{owner}]: ";
    chomp(my $uname = <STDIN>);
    $uname =~ s/\s.*//g;
    $uname = length($uname)?$uname:$opts{owner};
    print "Enter a character class for this account: ";
    chomp(my $uclass = <STDIN>);
    print "Enter a password for this account: ";
    if ($^O ne "MSWin32") {
        system("stty -echo");
    }
    chomp(my $upass = <STDIN>);
    if ($^O ne "MSWin32") {
        system("stty echo");
    }
    $rps{$uname}{pass} = crypt($upass,mksalt());
    $rps{$uname}{next} = $opts{rpbase};
    $rps{$uname}{level} = 0;
    $rps{$uname}{class} = substr($uclass,0,30);
    $rps{$uname}{created} = time();
    $rps{$uname}{lastlogin} = time();
    $rps{$uname}{x} = int(rand($opts{mapx}));
    $rps{$uname}{y} = int(rand($opts{mapy}));
    $rps{$uname}{alignment}="n";
    $rps{$uname}{gender} = "u";
    $rps{$uname}{nick} = "";
    $rps{$uname}{userhost} = "";
    $rps{$uname}{idled} = 0;
    $rps{$uname}{online} = 0;
    $rps{$uname}{isadmin} = 1;
    for my $item (0..$#items) {
        $rps{$uname}{item}[$item] = 0;
    }
    for my $pen ("pen_mesg","pen_nick","pen_part",
                 "pen_kick","pen_quit","pen_quest",
                 "pen_logout","pen_logout") {
        $rps{$uname}{$pen} = 0;
    }
    writedb();
    print "OK, wrote you into $opts{dbfile}.\n";
}

# this is almost silly...
my $versionhash;
my $gitdir=$0; $gitdir =~ s/[^\/]+$/.git/;
if ($opts{checkupdates} and -r "$gitdir/refs/heads/master") { 
    my $branch=`cat "$gitdir/HEAD"`; $branch=~s/ref: refs\/heads\/(\S+).*$/$1/s;
    $versionhash=`cat "$gitdir/refs/heads/$branch"`; chomp($versionhash);
    print "Checking for updates (at $versionhash)\n";
    my $tempsock = IO::Socket::INET->new(PeerAddr=>"fatphil.org:80",
                                         Timeout => 15);
    if ($tempsock) {
        print $tempsock "GET /git/idlerpg.git/refs/heads/master HTTP/1.1\r\n".
                        "Host: fatphil.org\r\n\r\n";
        my($line,$newversion);
        while ($line=<$tempsock>) {
            chomp($line);
            if ($line =~ /^([0-9a-f]+)$/) {
		print "You are ".($1 eq $versionhash ?"up to date\n":"NOT running the latest version (commit id $1).\n");
		last();
            }
        }
        close($tempsock);
    }
    else { print debug("Could not connect to update server.")."\n"; }
}

my %cmd_permissions=(
    (map {$_=>'admin'} qw/delold del brawl hog event rehash chpass chuser chclass push newquest die/,
     qw/reloaddb backup pause silent jump restart clearq eventtest/),
    peval=>'admin+ownerpevalonly', mkadmin=>'admin+owneraddonly', deladmin=>'admin+ownerdelonly',
    info=>'admin|allowuserinfo',
    );
sub cmd_admin_check($$) {
    my ($cmd,$username)=@_;
    # Always OK if we're the owner
    if(defined($username) and ($username eq $opts{owner})) { return 1; }
    # OK if admin not needed
    if(!exists($cmd_permissions{$cmd})) { return 1; }
    my $ex=$cmd_permissions{$cmd};
    # OK if opts enable this for anyone
    if($ex =~ m/^admin\|(allowuser\w+)$/) { return $opts{$1} ? 1 : ha($username); }
    # If permissions require admin with no modification, then we can bail
    if($ex =~ m/^admin$/) { return ha($username); }
    # So we're admin but not owner - is that a problem?
    if($ex =~ m/^admin\+(owner\w+only)/) { return $opts{$1} ? 0 : ha($username); }
    # Fail if we don't understand the exception?
    return length($ex) ? 0 : 1;
}
my %cmd_login_req=(map{$_=>1} qw/logout status whoami inventory newpass newclass align gender removeme/);
sub cmd_login_check($$) { return exists($cmd_login_req{$_[0]}) && !defined($_[1]); }

print "\n".debug(($opts{daemonize}?"B":"NOT b")."ecoming a daemon...")."\n";
daemonize() if($opts{daemonize});

$SIG{HUP} = "readconfig"; # sighup = reread config file

CONNECT: # cheese.

loaddb();

while (!$sock && $conn_tries < 2*@{$opts{servers}}) {
    debug("Connecting to $opts{servers}->[0]...");
    my %sockinfo = (PeerAddr => $opts{servers}->[0],
                    PeerPort => 6667);
    if ($opts{localaddr}) { $sockinfo{LocalAddr} = $opts{localaddr}; }
    $sock = IO::Socket::INET->new(%sockinfo) or
        debug("Error: failed to connect: $!\n");
    ++$conn_tries;
    if (!$sock) {
        # cycle front server to back if connection failed
        push(@{$opts{servers}},shift(@{$opts{servers}}));
    }
    else { debug("Connected."); }
}

if (!$sock) {
    debug("Error: Too many connection failures, exhausted server list.\n",1);
}

$conn_tries=0;

$sel = IO::Select->new($sock);

sts("NICK $opts{botnick}");
sts("USER $opts{botuser} 0 0 :$opts{botrlnm}");

while (1) {
    my($readable) = IO::Select->select($sel,undef,undef,0.5);
    if (defined($readable)) {
        my $fh = $readable->[0];
        my $buffer2;
        $fh->recv($buffer2,512,0);
        if (length($buffer2)) {
            $buffer .= $buffer2;
	    while ($buffer =~ s/^(.*?)\n//) {
                parse($1);
            }
        }
        else {
            # uh oh, we've been disconnected from the server, possibly before
            # we've logged in the users in %auto_login. so, we'll set those
            # users' online flags to 1, rewrite db, and attempt to reconnect
            # (if that's wanted of us)
            $rps{$_}{online}=1 for keys(%auto_login);
            writedb();

            close($fh);
            $sel->remove($fh);

            if ($opts{reconnect}) {
                undef(@queue);
                undef($sock);
                debug("Socket closed; disconnected. Cleared outgoing message ".
                      "queue. Waiting $opts{reconnect_wait}s before next ".
                      "connection attempt...");
                sleep($opts{reconnect_wait});
                goto CONNECT;
            }
            else { debug("Socket closed; disconnected.",1); }
        }
    }
    else { select(undef,undef,undef,1); }
    if ((time()-$lasttime) >= $opts{self_clock}) { rpcheck(); }
}

sub comma_list($) {
    my $l=$_[0];
    my $list=join(", ",@$l);
    if($#$l>1) { substr($list,-length($l->[-1]),0)='and '; } # last element modified
    elsif($#$l==1) { substr($list,-length($l->[-1])-2,1)=' and'; } # last ", " modified
    return $list;
}

sub parse {
    my($in) = shift;
    $inbytes += length($in); # increase parsed byte count
    $in =~ s/[\r\n]//g; # strip all \r and \n
    debug("<- $in");
    my @arg = split(/\s/,$in); # split into "words"
    my $usernick = substr((split(/!/,$arg[0]))[0],1);
    # logged in char name of nickname, or undef if nickname is not online
    my $username = finduser($usernick);
    if (lc($arg[0]) eq 'ping') { sts("PONG $arg[1]",1); }
    elsif (lc($arg[0]) eq 'error') {
        # uh oh, we've been disconnected from the server, possibly before we've
        # logged in the users in %auto_login. so, we'll set those users' online
        # flags to 1, rewrite db, and attempt to reconnect (if that's wanted of
        # us)
        $rps{$_}{online}=1 for keys(%auto_login);
        writedb();
        return;
    }
    $arg[1] = lc($arg[1]); # original case no longer matters
    if ($arg[1] eq '433' && $opts{botnick} eq $arg[3]) {
        $opts{botnick} .= 0;
        sts("NICK $opts{botnick}");
    }
    elsif ($arg[1] eq 'join') {
        # %onchan holds time user joined channel. used for the advertisement ban
        $onchan{$usernick}=time();
        if ($opts{detectsplits} && exists($split{substr($arg[0],1)})) {
            delete($split{substr($arg[0],1)});
        }
        elsif ($opts{botnick} eq $usernick) {
            sts("WHO $opts{botchan}");
            (my $opcmd = $opts{botopcmd}) =~ s/%(owner|botnick)%/$opts{$1}/eg;
            sts($opcmd);
            $lasttime = time(); # start rpcheck()
        }
    }
    elsif ($arg[1] eq 'quit') {
        # if we see our nick come open, grab it (skipping queue)
        if ($usernick eq $primnick) { sts("NICK $primnick",1); }
        elsif ($opts{detectsplits} &&
               "@arg[2..$#arg]" =~ /^:\S+\.\S+ \S+\.\S+$/) {
            if (defined($username)) { # user was online
                $split{substr($arg[0],1)}{time}=time();
                $split{substr($arg[0],1)}{account}=$username;
            }
        }
        else {
            penalize($username,"quit");
        }
        delete($onchan{$usernick});
    }
    elsif ($arg[1] eq 'nick') {
        # if someone (nickserv) changes our nick for us, update $opts{botnick}
        if ($usernick eq $opts{botnick}) {
            $opts{botnick} = substr($arg[2],1);
        }
        # if we see our nick come open, grab it (skipping queue), unless it was
        # us who just lost it
        elsif ($usernick eq $primnick) { sts("NICK $primnick",1); }
        else {
            penalize($username,"nick",$arg[2]);
            $onchan{substr($arg[2],1)} = delete($onchan{$usernick});
        }
    }
    elsif ($arg[1] eq 'part') {
        penalize($username,"part");
        delete($onchan{$usernick});
    }
    elsif ($arg[1] eq 'kick') {
        $usernick = $arg[3];
        penalize(finduser($usernick),"kick");
        delete($onchan{$usernick});
    }
    # don't penalize /notices to the bot
    elsif ($arg[1] eq 'notice' && $arg[2] ne $opts{botnick}) {
        penalize($username,"notice",length("@arg[3..$#arg]")-1);
    }
    elsif ($arg[1] eq '001') {
        # send our identify command, set our usermode, join channel
        (my $identcmd = $opts{botident}) =~ s/%(owner|botnick)%/$opts{$1}/eg;
        sts($identcmd);
        sts("MODE $opts{botnick} :$opts{botmodes}");
        sts("JOIN $opts{botchan}");
        $opts{botchan} =~ s/ .*//; # strip channel key if present
    }
    elsif ($arg[1] eq '315') {
        # 315 is /WHO end. report who we automagically signed online iff it will
        # print < 1k of text
        if (keys(%auto_login)) {
            # not a true measure of size, but easy
	    chanmsg("Recognised ". scalar(keys(%auto_login))." users on channel. ".
		    "Automatically logging " .
		    ((length("%auto_login") < 1024 && $opts{senduserlist})
		     ? "in accounts: ".join(", ",keys(%auto_login))
		     : "them in."));
            if ($opts{voiceonlogin}) {
                my @vnicks = map { $rps{$_}{nick} } keys(%auto_login);
                while (@vnicks) {
                    my @removed = splice(@vnicks,0,$opts{modesperline});
                    sts("MODE $opts{botchan} +".
                        ('v' x scalar(@removed))." ".
                        join(" ",@removed));
                }
            }
        }
        else { chanmsg("0 users qualified for auto login."); }
        undef(%prev_online);
        undef(%auto_login);
    }
    elsif ($arg[1] eq '005') {
        if ("@arg" =~ /MODES=(\d+)/) { $opts{modesperline}=$1; }
    }
    elsif ($arg[1] eq '352') {
        my $user;
        # 352 is one line of /WHO. check that the nick!user@host exists as a key
        # in %prev_online, the list generated in loaddb(). the value is the user
        # to login
        $onchan{$arg[7]}=time();
        if (exists($prev_online{$arg[7]."!".$arg[4]."\@".$arg[5]})) {
            $rps{$prev_online{$arg[7]."!".$arg[4]."\@".$arg[5]}}{online} = 1;
            $auto_login{$prev_online{$arg[7]."!".$arg[4]."\@".$arg[5]}}=1;
        }
    }
    elsif ($arg[1] eq 'privmsg') {
        $arg[0] = substr($arg[0],1); # strip leading : from privmsgs
        if (lc($arg[2]) eq lc($opts{botnick})) { # to us, not channel
            $arg[3] = lc(substr($arg[3],1)); # lowercase, strip leading :
	    if(!cmd_admin_check($arg[3],$username)) {
		privmsg("You don't have access to ".uc($arg[3]).".", $usernick);
	    }
	    elsif (cmd_login_check($arg[3],$username)) {
		privmsg("You are not logged in.", $usernick);
	    }
	    elsif ($arg[3] eq "\1version\1") {
                notice("\1VERSION IRPG bot v$version by jotun; ".
                       "http://idlerpg.net/\1",$usernick);
            }
            elsif ($arg[3] eq "peval") {
		my @peval = eval "@arg[4..$#arg]";
		if (@peval >= 4 || length("@peval") > 1024) {
		    privmsg("Command produced too much output to send ".
			    "outright; queueing ".length("@peval").
			    " bytes in ".scalar(@peval)." items. Use ".
			    "CLEARQ to clear queue if needed.",$usernick,1);
		    privmsg("$_",$usernick) for @peval;
		}
		else { privmsg("$_",$usernick, 1) for @peval; }
		privmsg("EVAL ERROR: $@", $usernick, 1) if $@;
            }
            elsif ($arg[3] eq "register") {
                if (defined $username) {
                    privmsg("Sorry, you are already online as $username.",
                            $usernick);
                }
                else {
                    if ($#arg < 6 || $arg[6] eq "") {
                        privmsg("Try: REGISTER <char name> <password> <class>",
                                $usernick);
                        privmsg("IE : REGISTER Poseidon MyPassword God of the ".
                                "Sea",$usernick);
                    }
                    elsif ($pausemode) {
                        privmsg("Sorry, new accounts may not be registered ".
                                "while the bot is in pause mode; please wait ".
                                "a few minutes and try again.",$usernick);
                    }
                    elsif (exists $rps{$arg[4]} || ($opts{casematters} &&
                           scalar(grep { lc($arg[4]) eq lc($_) } keys(%rps)))) {
                        privmsg("Sorry, that character name is already in use.",
                                $usernick);
                    }
                    elsif (lc($arg[4]) eq lc($opts{botnick}) ||
                           lc($arg[4]) eq lc($primnick)) {
                        privmsg("Sorry, that character name cannot be ".
                                "registered.",$usernick);
                    }
                    elsif (!exists($onchan{$usernick})) {
                        privmsg("Sorry, you're not in $opts{botchan}.",
                                $usernick);
                    }
                    elsif (length($arg[4]) > 16 || length($arg[4]) < 1) {
                        privmsg("Sorry, character names must be < 17 and > 0 ".
                                "chars long.", $usernick);
                    }
                    elsif ($arg[4] =~ /^#/) {
                        privmsg("Sorry, character names may not begin with #.",
                                $usernick);
                    }
                    elsif ($arg[4] =~ /\001/) {
                        privmsg("Sorry, character names may not include ".
                                "character \\001.",$usernick);
                    }
                    elsif ($opts{noccodes} && ($arg[4] =~ /[[:cntrl:]]/ ||
                           "@arg[6..$#arg]" =~ /[[:cntrl:]]/)) {
                        privmsg("Sorry, neither character names nor classes ".
                                "may include control codes.",$usernick);
                    }
                    elsif ($opts{nononp} && ($arg[4] =~ /[[:^print:]]/ ||
                           "@arg[6..$#arg]" =~ /[[:^print:]]/)) {
                        privmsg("Sorry, neither character names nor classes ".
                                "may include non-printable chars.",$usernick);
                    }
                    elsif (length("@arg[6..$#arg]") > 30) {
                        privmsg("Sorry, character classes must be < 31 chars ".
                                "long.",$usernick);
                    }
                    elsif (time() == $lastreg) {
                        privmsg("Wait 1 second and try again.",$usernick);
                    }
                    else {
                        if ($opts{voiceonlogin}) {
                            sts("MODE $opts{botchan} +v :$usernick");
                        }
			my $uname=$arg[4];
			++$registrations;
			$lastreg = time();
			$rps{$uname}{pass} = crypt($arg[5],mksalt());
			$rps{$uname}{next} = $opts{rpbase};
			$rps{$uname}{level} = 0;
			$rps{$uname}{class} = "@arg[6..$#arg]";
			$rps{$uname}{created} = time();
			$rps{$uname}{lastlogin} = time();
			$rps{$uname}{x} = int(rand($opts{mapx}));
			$rps{$uname}{y} = int(rand($opts{mapy}));
			$rps{$uname}{alignment}="n";
			$rps{$uname}{gender}="u";
			$rps{$uname}{nick} = $usernick;
			$rps{$uname}{userhost} = $arg[0];
			$rps{$uname}{online} = 1;
			$rps{$uname}{isadmin} = 0;
			for my $item (0..$#items) {
			    $rps{$uname}{item}[$item] = 0;
			}
			for my $pen ("pen_mesg","pen_nick","pen_part",
				     "pen_kick","pen_quit","pen_quest",
				     "pen_logout","pen_logout") {
			    $rps{$uname}{$pen} = 0;
			}
			chanmsg("Welcome $usernick\'s new player $uname, the ".
				"@arg[6..$#arg]! Next level in ".
				duration($opts{rpbase}).".");
			privmsg("Success! Account $uname created. You have ".
				"$opts{rpbase} seconds idleness until you ".
				"reach level 1. ", $usernick);
                        privmsg("NOTE: The point of the game is to see who ".
                                "can idle the longest. As such, talking in ".
                                "the channel, parting, quitting, and changing ".
                                "nicks all penalize you.",$usernick);
                        if ($opts{phonehome}) {
                            my $tempsock = IO::Socket::INET->new(PeerAddr=>
                                "jotun.ultrazone.org:80");
                            if ($tempsock) {
                                print $tempsock
                                    "GET /g7/count.php?new=1 HTTP/1.1\r\n".
                                    "Host: jotun.ultrazone.org:80\r\n\r\n";
                                sleep(1);
                                close($tempsock);
                            }
                        }
                    }
                }
            }
            elsif ($arg[3] eq "delold") {
                # insure it is a number
		if ($arg[4] !~ /^[\d\.]+$/) {
                    privmsg("Try: DELOLD <# of days>", $usernick, 1);
                }
                else {
                    my @oldaccounts = grep { (time()-$rps{$_}{lastlogin}) >
                                             ($arg[4] * 86400) &&
                                             !$rps{$_}{online} } keys(%rps);
                    delete(@rps{@oldaccounts});
                    chanmsg(scalar(@oldaccounts)." accounts not accessed in ".
                            "the last $arg[4] days removed by $arg[0].");
                }
            }
            elsif ($arg[3] eq "del") {
		if (!defined($arg[4])) {
                   privmsg("Try: DEL <char name>", $usernick, 1);
                }
                elsif (!exists($rps{$arg[4]})) {
                    privmsg("No such account $arg[4].", $usernick, 1);
                }
                else {
                    delete($rps{$arg[4]});
                    chanmsg("Account $arg[4] removed by $arg[0].");
                }
            }
            elsif ($arg[3] eq "mkadmin") {
		if (!defined($arg[4])) {
                    privmsg("Try: MKADMIN <char name>", $usernick, 1);
                }
                elsif (!exists($rps{$arg[4]})) {
                    privmsg("No such account $arg[4].", $usernick, 1);
                }
                else {
                    $rps{$arg[4]}{isadmin}=1;
                    privmsg("Account $arg[4] is now a bot admin.",$usernick, 1);
                }
            }
            elsif ($arg[3] eq "deladmin") {
		if (!defined($arg[4])) {
                    privmsg("Try: DELADMIN <char name>", $usernick, 1);
                }
                elsif (!exists($rps{$arg[4]})) {
                    privmsg("No such account $arg[4].", $usernick, 1);
                }
                elsif ($arg[4] eq $opts{owner}) {
                    privmsg("Cannot DELADMIN owner account.", $usernick, 1);
                }
                else {
                    $rps{$arg[4]}{isadmin}=0;
                    privmsg("Account $arg[4] is no longer a bot admin.",
                            $usernick, 1);
                }
            }
            elsif ($arg[3] eq "brawl") {
		my $updown = (defined($arg[4]) && $arg[4] eq 'evil') ? 1 : -1;
		my %desc=(-1=>'righteous duel', 1=>'bloodthirsty brawl'); #civilised
		chanmsg("$usernick has brought about a $desc{$updown}.");
		brawl($updown);
            }
            elsif ($arg[3] eq "hog") {
		chanmsg("$usernick has summoned the Hand of God.");
		hog();
            }
            elsif ($arg[3] eq "event") {
		my $updown = defined($arg[4]) ? ($arg[4] eq 'good') - ($arg[4] eq 'bad') : 0;
		my %desc=(-1 => 'bad', 1 => 'good', 0 => 'random');
		chanmsg("$usernick has brought about a $desc{$updown} event.");
		modify_item($updown || (rand()>0.5)*2-1);
            }
            elsif ($arg[3] eq "rehash") {
		readconfig();
		read_items();
		read_events();
		privmsg("Reread config file, items, and events.",$usernick,1);
		$opts{botchan} =~ s/ .*//; # strip channel key if present
            }
            elsif ($arg[3] eq "chpass") {
		if (!defined($arg[5])) {
                    privmsg("Try: CHPASS <char name> <new pass>", $usernick, 1);
                }
                elsif (!exists($rps{$arg[4]})) {
                    privmsg("No such username $arg[4].", $usernick, 1);
                }
                else {
                    $rps{$arg[4]}{pass} = crypt($arg[5],mksalt());
                    privmsg("Password for $arg[4] changed.", $usernick, 1);
                }
            }
            elsif ($arg[3] eq "chuser") {
		if (!defined($arg[5])) {
                    privmsg("Try: CHUSER <char name> <new char name>",
                            $usernick, 1);
                }
                elsif (!exists($rps{$arg[4]})) {
                    privmsg("No such username $arg[4].", $usernick, 1);
                }
                elsif (exists($rps{$arg[5]})) {
                    privmsg("Username $arg[5] is already taken.", $usernick,1);
                }
                else {
                    $rps{$arg[5]} = delete($rps{$arg[4]});
                    privmsg("Username for $arg[4] changed to $arg[5].",
                            $usernick, 1);
                }
            }
            elsif ($arg[3] eq "chclass") {
		if (!defined($arg[5])) {
                    privmsg("Try: CHCLASS <char name> <new char class>",
                            $usernick, 1);
                }
                elsif (!exists($rps{$arg[4]})) {
                    privmsg("No such username $arg[4].", $usernick, 1);
                }
                else {
                    $rps{$arg[4]}{class} = "@arg[5..$#arg]";
                    privmsg("Class for $arg[4] changed to @arg[5..$#arg].",
                            $usernick, 1);
                }
            }
            elsif ($arg[3] eq "push") {
                # insure it's a positive or negative, integral number of seconds
		if ($arg[5] !~ /^\-?\d+$/) {
                    privmsg("Try: PUSH <char name> <seconds>", $usernick, 1);
                }
                elsif (!exists($rps{$arg[4]})) {
                    privmsg("No such username $arg[4].", $usernick, 1);
                }
                elsif ($arg[5] > $rps{$arg[4]}{next}) {
                    privmsg("Time to level for $arg[4] ($rps{$arg[4]}{next}s) ".
                            "is lower than $arg[5]; setting TTL to 0.",
                            $usernick, 1);
                    chanmsg_l("$usernick has pushed $arg[4] $rps{$arg[4]}{next} ".
                              "seconds toward level ".($rps{$arg[4]}{level}+1));
                    $rps{$arg[4]}{next}=0;
                }
                else {
                    $rps{$arg[4]}{next} -= $arg[5];
                    chanmsg_l("$usernick has pushed $arg[4] $arg[5] seconds ".
                              "toward level ".($rps{$arg[4]}{level}+1).". ".
                              "$arg[4] reaches next level in ".
                              duration($rps{$arg[4]}{next}).".");
                }
            }
            elsif ($arg[3] eq "logout") {
		penalize($username,"logout");
            }
            elsif ($arg[3] eq "newquest") {
		if(@{$quest{questers}}) {
                    privmsg("There is already a quest.",$usernick);
                }
                else {
                    privmsg("A new quest will start shortly.",$usernick);
                    $quest{qtime} = time(); # schedule it for now
                }
            }
            elsif ($arg[3] eq "quest") {
                if (!@{$quest{questers}}) {
                    privmsg("There is no active quest.",$usernick);
                }
		elsif ($quest{type} == 1) {
		    privmsg("$quest{text} Quest to complete in ".
			    duration($quest{qtime}-time()).".", $usernick);
		}
		elsif ($quest{type} == 2) {
		    privmsg("$quest{text} Participants must first reach ".
			    "[$quest{p1}->[0],$quest{p1}->[1]], then ".
			    "[$quest{p2}->[0],$quest{p2}->[1]].".
			    ($opts{mapurl}?" See $opts{mapurl} to monitor ".
			     "their journey's progress.":""), $usernick);
		}
            }
            elsif ($arg[3] eq "status" && $opts{statuscmd}) {
                # argument is optional
		if ($arg[4] && !exists($rps{$arg[4]})) {
                    privmsg("No such user.",$usernick);
                }
                else {
		    my $u=$arg[4]//$username;
                    privmsg("$u: Level $rps{$u}{level} ".
                            "$rps{$u}{class}; Status: O".
                            ($rps{$u}{online}?"n":"ff")."line; ".
                            "TTL: ".duration($rps{$u}{next})."; ".
                            "Idled: ".duration($rps{$u}{idled}).
                            "; Item sum: ".itemsum($u),$usernick);
                }
            }
            elsif ($arg[3] eq "whoami") {
		privmsg("You are $username, the level ".
			$rps{$username}{level}." $rps{$username}{class}. ".
			"Next level in ".duration($rps{$username}{next}),
			$usernick);
            }
            elsif ($arg[3] eq "inventory") {
		my @list = map { item_describe($_,$rps{$username}{item}[$_],1,1); }(0..$#items);
		privmsg("You are carrying ". comma_list(\@list), $usernick);
            }
            elsif ($arg[3] eq "newpass") {
		if (!defined($arg[4])) {
                    privmsg("Try: NEWPASS <new password>", $usernick);
                }
                else {
                    $rps{$username}{pass} = crypt($arg[4],mksalt());
                    privmsg("Your password was changed.",$usernick);
                }
            }
            elsif ($arg[3] eq "newclass") {
                if (!defined($arg[4])) {
                    privmsg("Try: NEWCLASS <new class>", $usernick);
                }
                else {
                    $rps{$username}{class} = "@arg[4..$#arg]";
                    privmsg("Class for $username changed to @arg[4..$#arg].",
                            $usernick, 1);
                }
            }
            elsif ($arg[3] eq "align") {
                if (!defined($arg[4]) ||
		    (lc($arg[4]) ne "good" && lc($arg[4]) ne "neutral" && lc($arg[4]) ne "evil")) {
                    privmsg("Try: ALIGN <good|neutral|evil>", $usernick);
                }
                else {
                    $rps{$username}{alignment} = substr(lc($arg[4]),0,1);
                    chanmsg("$username has changed alignment to: ".lc($arg[4]).
                            ".");
                    privmsg("Your alignment was changed to ".lc($arg[4]).".",
                            $usernick);
                }
            }
            elsif ($arg[3] eq "gender") {
		if (!defined($arg[4]) || !defined($hesheit{lc($arg[4])})) {
                    privmsg("Try: GENDER <m|f|n|u|pc>", $usernick);
                }
                else {
                    $rps{$username}{gender} = lc($arg[4]);
                    chanmsg("$username has changed gender to: ".lc($arg[4]).".");
                    privmsg("Your gender was changed to ".lc($arg[4]).".",
                            $usernick);
                }
            }
            elsif ($arg[3] eq "removeme") {
		privmsg("Account $username removed.",$usernick);
		chanmsg("$arg[0] removed his account, $username, the ".
			$rps{$username}{class}.".");
		delete($rps{$username});
            }
            elsif ($arg[3] eq "help") {
                if (!ha($username)) {
                    privmsg("For information on IRPG bot commands, see ".
                            $opts{helpurl}, $usernick);
                }
                else {
                    privmsg("Help URL is $opts{helpurl}", $usernick, 1);
                    privmsg("Admin commands URL is $opts{admincommurl}",
                            $usernick, 1);
                }
            }
            elsif ($arg[3] eq "die") {
		$opts{reconnect} = 0;
		writedb();
		sts("QUIT :DIE ".($#arg>3?"'@arg[4..$#arg]' ":'')."from $usernick",1);
            }
            elsif ($arg[3] eq "reloaddb") {
		if (!$pausemode) {
                    privmsg("ERROR: Can only use LOADDB while in PAUSE mode.",
                            $usernick, 1);
                }
                else {
                    loaddb();
                    privmsg("Reread player database file; ".scalar(keys(%rps)).
                            " accounts loaded.",$usernick,1);
                }
            }
            elsif ($arg[3] eq "backup") {
		backup();
		privmsg("$opts{dbfile} copied to ".
			".dbbackup/$opts{dbfile}".time(),$usernick,1);
            }
            elsif ($arg[3] eq "pause") {
		$pausemode = $pausemode ? 0 : 1;
		privmsg("PAUSE_MODE set to $pausemode.",$usernick,1);
            }
            elsif ($arg[3] eq "silent") {
		if (!defined($arg[4]) || $arg[4] < 0 || $arg[4] > 3) {
                    privmsg("Try: SILENT <mode>", $usernick,1);
                }
                else {
                    $silentmode = $arg[4];
                    privmsg("SILENT_MODE set to $silentmode.",$usernick,1);
                }
            }
            elsif ($arg[3] eq "jump") {
		if (!defined($arg[4])) {
                    privmsg("Try: JUMP <server[:port]>", $usernick, 1);
                }
                else {
                    writedb();
                    sts("QUIT :JUMP to $arg[4] from $arg[0]");
                    unshift(@{$opts{servers}},$arg[4]);
                    close($sock);
                    sleep(3);
                    goto CONNECT;
                }
            }
            elsif ($arg[3] eq "restart") {
		writedb();
		sts("QUIT :RESTART ".($#arg>3?"'@arg[4..$#arg]' ":'')."from $usernick",1);
		close($sock);
		exec("perl $0");
            }
            elsif ($arg[3] eq "clearq") {
		undef(@queue);
		chanmsg("Outgoing message queue cleared by $arg[0].");
		privmsg("Outgoing message queue cleared.",$usernick,1);
            }
            elsif ($arg[3] eq "info") {
                my $info;
                if (!ha($username) && $opts{allowuserinfo}) {
		    my $hash=$versionhash?(" (".substr($versionhash,0,12).")"):'';
		    $info = "IRPG bot v$version$hash by jotun et al., ".
                            "http://idlerpg.net/. On via server: ".
                            $opts{servers}->[0].". Admins online: ".
                            join(", ", map { $rps{$_}{nick} }
                                      grep { $rps{$_}{isadmin} &&
                                             $rps{$_}{online} } keys(%rps)).".";
                    privmsg($info, $usernick);
                }
                elsif (!ha($username) && !$opts{allowuserinfo}) {
                    privmsg("You do not have access to INFO.", $usernick);
                }
                else {
                    my $queuedbytes = 0;
                    $queuedbytes += (length($_)+2) for @queue; # +2 = \r\n
                    $info = sprintf(
                        "%.2fkb sent, %.2fkb received in %s. %d IRPG users ".
                        "online of %d total users. %d accounts created since ".
                        "startup. PAUSE_MODE is %d, SILENT_MODE is %d. ".
                        "Outgoing queue is %d bytes in %d items. On via: %s. ".
                        "Admins online: %s.",
                        $outbytes/1024,
                        $inbytes/1024,
                        duration(time()-$^T),
                        scalar(grep { $rps{$_}{online} } keys(%rps)),
                        scalar(keys(%rps)),
                        $registrations,
                        $pausemode,
                        $silentmode,
                        $queuedbytes,
                        scalar(@queue),
                        $opts{servers}->[0],
                        join(", ",map { $rps{$_}{nick} }
                                  grep { $rps{$_}{isadmin} && $rps{$_}{online} }
                                  keys(%rps)));
                    privmsg($info, $usernick, 1);
                }
            }
            elsif ($arg[3] eq "login") {
                if (defined($username)) {
                    notice("Sorry, you are already online as $username.",
                            $usernick);
                }
                else {
                    if ($#arg < 5 || $arg[5] eq "") {
                        notice("Try: LOGIN <username> <password>", $usernick);
                    }
                    elsif (!exists $rps{$arg[4]}) {
                        notice("Sorry, no such account name. Note that ".
                                "account names are case sensitive.",$usernick);
                    }
                    elsif (!exists $onchan{$usernick}) {
                        notice("Sorry, you're not in $opts{botchan}.",
                                $usernick);
                    }
                    elsif ($rps{$arg[4]}{pass} ne
                           crypt($arg[5],$rps{$arg[4]}{pass})) {
                        notice("Wrong password.", $usernick);
                    }
                    else {
                        if ($opts{voiceonlogin}) {
                            sts("MODE $opts{botchan} +v :$usernick");
                        }
                        $rps{$arg[4]}{online} = 1;
                        $rps{$arg[4]}{nick} = $usernick;
                        $rps{$arg[4]}{userhost} = $arg[0];
                        $rps{$arg[4]}{lastlogin} = time();
                        chanmsg("$arg[4], the level $rps{$arg[4]}{level} ".
                                "$rps{$arg[4]}{class}, is now online from ".
                                "nickname $usernick. Next level in ".
                                duration($rps{$arg[4]}{next}).".");
                        notice("Logon successful. Next level in ".
                               duration($rps{$arg[4]}{next}).".", $usernick);
                    }
                }
            }
            elsif ($arg[3] eq 'itemlevel') { # debugging aid
		my ($ok, $typeid, $level, $nlevel) = ($arg[4] =~ /^(\d+)([a-z])$/)
		    ? (defined($uniques[$uniques{$2}]), $uniques[$uniques{$2}]->{typeid}, $arg[4], $1)
		    : (1, $arg[4], $arg[5], $arg[5]);
		if(!$ok or $typeid<0 or $typeid>$#items or $nlevel<0 or $nlevel>999) {
		    notice("0 <= item <= $#items, 0 <= level <= 999", $usernick);
		}
		else {
		    notice("itemlevel($typeid,$level) = ".item_describe($typeid,$level,0,1),
			   $usernick); 
		}
            }
	    elsif ($arg[3] eq 'eventtest' and $arg[4] =~ /^([WLGCHE])$/i) {
		my $t=$1;
		my @p = ($arg[5]//'name1');
		if($t=~/H/) { push(@p, $arg[6]//'name2'); }
		notice(($t=~/[GC]/i?"$p[0] ":'').get_event($t, \@p, rand()), $usernick);
	    }
        }
        # penalize returns true if user was online and successfully penalized.
        # if the user is not logged in, then penalize() fails. so, if user is
        # offline, and they say something including "http:", and they've been on
        # the channel less than 90 seconds, and the http:-style ban is on, then
        # check to see if their url is in @{$opts{okurl}}. if not, kickban them
        elsif (!penalize($username,"privmsg",length("@arg[3..$#arg]")) &&
               index(lc("@arg[3..$#arg]"),"http:") != -1 &&
               (time()-$onchan{$usernick}) < 90 && $opts{doban}) {
            my $isokurl = 0;
            for (@{$opts{okurl}}) {
                if (index(lc("@arg[3..$#arg]"),lc($_)) != -1) { $isokurl = 1; }
            }
            if (!$isokurl) {
                sts("MODE $opts{botchan} +b $arg[0]");
                sts("KICK $opts{botchan} $usernick :No advertising; ban will ".
                    "be lifted within the hour.");
                push(@bans,$arg[0]) if @bans < 12;
            }
        }
    }
}

sub sts { # send to server
    my($text,$skipq) = @_;
    if ($skipq) {
        if ($sock) {
            print $sock "$text\r\n";
            $outbytes += length($text) + 2;
            debug("-> $text");
        }
        else {
            # something is wrong. the socket is closed. clear the queue
            undef(@queue);
            debug("\$sock isn't writeable in sts(), cleared outgoing queue.\n");
            return;
        }
    }
    else {
        push(@queue,$text);
        debug(sprintf("(q%03d) = %s\n",$#queue,$text));
    }
}

sub fq { # deliver message(s) from queue
    if (!@queue) {
        ++$freemessages if $freemessages < 4;
        return undef;
    }
    my $sentbytes = 0;
    for (0..$freemessages) {
        last() if !@queue; # no messages left to send
        # lower number of "free" messages we have left
        my $line=shift(@queue);
        # if we have already sent one message, and the next message to be sent
        # plus the previous messages we have sent this call to fq() > 768 bytes,
        # then requeue this message and return. we don't want to flood off,
        # after all
        if ($_ != 0 && (length($line)+$sentbytes) > 768) {
            unshift(@queue,$line);
            last();
        }
        if ($sock) {
            debug("(fm$freemessages) -> $line");
            --$freemessages if $freemessages > 0;
            print $sock "$line\r\n";
            $sentbytes += length($line) + 2;
        }
        else {
            undef(@queue);
            debug("Disconnected: cleared outgoing message queue.");
            last();
        }
        $outbytes += length($line) + 2;
    }
}

sub ttl( $ ) {
    my $lvl = $_[0];
    return ($opts{rpbase} * ($opts{rpstep}**$lvl)) if $lvl <= 60;
    return (($opts{rpbase} * ($opts{rpstep}**60)) + (86400*($lvl - 60)));
}

sub duration { # return human duration of seconds
    my $s = shift;
    return "NA ($s)" if $s !~ /^\d+$/;
    return sprintf("%d day%s, %02d:%02d:%02d",$s/86400,int($s/86400)==1?"":"s",
                   ($s%86400)/3600,($s%3600)/60,($s%60));
}

sub unique_describe($$) { # uref, level
    my ($uref, $level)=@_;
    my $string=$uref->{desc};
    my $haslevel = ($string =~ s/%ulevel%/$_[1]/g);
    return ($haslevel ? '' : "level $_[1] ") . $string;
}
sub plain_describe($$) { # typeid, level
    my ($typeid,$level) = @_;
    if(!defined($levels[$typeid])) { return "level $level"; }
    my ($lev,$ind)=(-1,-1);
    my ($marker,$op,$deltaset,$deltasetlen,$deltaind,$marklast,$prec);
    while($lev<$level) {
	#print STDERR ("$lev<$level, ind=$ind".
	#              ($delta?", stepping=($marker,$op,$delta,$marklast)\n":"\n"));
        ++$lev;
        if($op) {
	    my $delta=$deltaset->[$deltaind];
            $marker = ($op eq '+') ? $marker+$delta 
                : ($op eq '-') ? $marker-$delta 
                : $marker*$delta;
            # Ensure accuracy is sensibly represented at every step, 
            # as we need to check our bounds correctly, and don't
            # want errors to accumulate.
	    $marker=sprintf("%.${prec}f", $marker);
	    $deltaind=($deltaind+1)%$deltasetlen;
            if(defined($marklast) && 
               (($op eq '-') ? $marker<=$marklast : $marker>=$marklast)) {
                undef($op); 
            }
        }
        else {
            ++$ind;
            if($levels[$typeid][$ind] =~ /%{([\d.]+)\#([-+*])([\d.:]+)(?:\#([\d.]+))?}%/) {
		my $deltaall;
                ($marker,$op,$deltaall,$marklast) = ($1,$2,$3,$4);
		$deltaset=[split(':',$deltaall)];
		$deltasetlen=scalar(@$deltaset);
		$deltaind=0;
		$prec=($deltasetlen==1?$deltaset->[0]:$marker) !~ m/\.(\d+)/ ? 0 : length($1);
            }
        }
    }
    my $template = $levels[$typeid][$ind];
    if(defined($marker)) {
        $template =~ s/%{([\d.]+)\#([-+*])([\d.:]+)(?:\#([\d.]+))?}%/$marker/;
    }
    return $template;
}
sub item_describe($$$$) { # typeid, level, article, saytype
    my ($typeid,$level,$article,$saytype)=@_;
    my $desc;
    if($_[1] =~ m/^(\d+)([a-z])/) {
	$desc = unique_describe($uniques[$uniques{$2}], int($1));
	$article = $article?"the ":'';
	$saytype=0; # presume uniques always include some kind of type
    } else {
	$desc = plain_describe($_[0], int($_[1]));
	$article = $article?"a ":'';
    }
    if($desc !~ s/^!a // and $article) {
	if(lc($article) eq 'a ' and $desc =~ /^[aeiouy18]/ and
	   $desc !~ /^(?:1(?:[^18][^0-9]|[0-9][0-9])|e[uw]|onc?e|uni[^nmd]|u[bcfhjkqrst][aeiou])/) {
	    substr($article,1,0) = 'n'; # would also work for A/An
	}
	$desc = $article . $desc;
    }
    my $type=$items[$typeid];
    my %types = ( type=>$type, Type=>ucfirst($type), TYPE=>uc($type), notype=>'' );
    if($desc !~ s/%((?:no|)type)%/$types{$1}/ig and $saytype) { $desc .= " $items[$typeid]"; }
    return $desc;
}
sub user_item($$) {
    return $rps{$_[0]}{item}[$_[1]];
}
sub item_val($) {
    $_[0] =~ /^(\d+)/;
    return $1;
}

sub user_item_val($$) {
    return item_val(user_item($_[0], $_[1]));
}

sub ts { # timestamp
    my @ts = localtime(time());
    return sprintf("[%02d/%02d/%02d %02d:%02d:%02d] ",
                   $ts[4]+1,$ts[3],$ts[5]%100,$ts[2],$ts[1],$ts[0]);
}

sub hog { # summon the hand of god
    my @players = grep { $rps{$_}{online} } keys(%rps);
    my $player = $players[rand(@players)];
    my $win = !!int(rand(5));
    my $rand = rand();
    my $time = int(((5 + int($rand*71))/100) * $rps{$player}{next});
    my $event = get_event($win?'W':'L', [$player], $rand);
    chanmsg_l("$event ".duration($time)." $tofrom[$win] level ".
              ($rps{$player}{level}+1).".");
    $rps{$player}{next} += $win ? -$time : $time;
    chanmsg("$player reaches next level in ".duration($rps{$player}{next}).".");
}

sub rpcheck { # check levels, update database
    # check splits hash to see if any split users have expired
    checksplits() if $opts{detectsplits};
    # send out $freemessages lines of text from the outgoing message queue
    fq();
    # clear registration limiting
    $lastreg = 0;
    my $online = scalar(grep { $rps{$_}{online} } keys(%rps));
    # there's really nothing to do here if there are no online users
    return unless $online;
    my $onlineevil = scalar(grep { $rps{$_}{online} &&
                                   $rps{$_}{alignment} eq "e" } keys(%rps));
    my $onlinegood = scalar(grep { $rps{$_}{online} &&
                                   $rps{$_}{alignment} eq "g" } keys(%rps));
    if (!$opts{noscale}) {
        if (rand((20*86400)/$opts{self_clock}) < $online) { hog(); }
        if (rand((24*86400)/$opts{self_clock}) < $online) { team_battle(); }
        if (rand((8*86400)/$opts{self_clock}) < $online) { calamity(); }
        if (rand((4*86400)/$opts{self_clock}) < $online) { godsend(); }
    }
    else {
        hog() if rand(4000) < 1;
        team_battle() if rand(4000) < 1;
        calamity() if rand(4000) < 1;
        godsend() if rand(2000) < 1;
    }
    if (rand((8*86400)/$opts{self_clock}) < $onlineevil) { evilness(); }
    if (rand((12*86400)/$opts{self_clock}) < $onlinegood) { holiness(); }

    moveplayers();
    process_items() if($opts{rpitembase});

    # statements using $rpreport do not bother with scaling by the clock because
    # $rpreport is adjusted by the number of seconds since last rpcheck()
    if (report_threshold(120) && $opts{questfilename}) { writequestfile(); }
    if (defined($quest{qtime}) and time() > $quest{qtime}) {
        if (!@{$quest{questers}}) { quest(); }
        elsif ($quest{type} == 1) {
	    chanmsg_l(get_event("QS",$quest{questers},undef));
            for (@{$quest{questers}}) {
                $rps{$_}{next} = int($rps{$_}{next} * .75);
            }
            undef(@{$quest{questers}});
            $quest{qtime} = time() + 21600;
        }
        # quest type 2 awards are handled in moveplayers()
    }
    if ($rpreport && report_threshold(43200)) { # twice-daily penance
	my @repentant = grep { $rps{$_}{online} &&
			     # $rps{$_}{alignment} ne 'e' &&
			       $rps{$_}{next} > 2*ttl($rps{$_}{level}) &&
			       $rps{$_}{level} > 0; } keys(%rps);
	for my $r (@repentant) {
	    # Supplication may make a comment about the current level
	    my $supplication = get_event('P'.uc($rps{$r}{alignment}), [$r], undef);
	    # Penance may make a comment about the destination level
	    $rps{$r}{level}--;
	    my $penance = get_event('P', [$r], undef);
	    chanmsg_l("$supplication $penance");
	    $rps{$r}{next} = int(ttl($rps{$r}{level}));
	}
    }				 
    if ($rpreport && report_threshold($opts{top_period}//36000)) { # default 10 hours
        my @u = sort { $rps{$b}{level} <=> $rps{$a}{level} ||
                       $rps{$a}{next}  <=> $rps{$b}{next} } keys(%rps);
        chanmsg("Idle RPG Top Players:") if @u;
        for my $i (0..2) {
            $#u >= $i and
            chanmsg("$u[$i], the level $rps{$u[$i]}{level} ".
                    "$rps{$u[$i]}{class}, is #" . ($i + 1) . "! Next level in ".
                    (duration($rps{$u[$i]}{next})).".");
        }
        backup();
    }
    if ($rpreport && report_threshold($opts{chal_period}//3600)) { # 1 hour
        my @players = grep { $rps{$_}{online} &&
                             $rps{$_}{level} > 44 } keys(%rps);
        # 20% of all players must be level 45+
        if ((scalar(@players)/scalar(grep { $rps{$_}{online} } keys(%rps))) > .15) {
            challenge_opp($players[int(rand(@players))]);
        }
    }
    if ($rpreport && report_threshold(3600)) { # 1 hour
        while (@bans) {
            sts("MODE $opts{botchan} -bbbb :@bans[0..3]");
            splice(@bans,0,4);
        }
    }
    if (report_threshold(1800)) { # 30 mins
        if ($opts{botnick} ne $primnick) {
            (my $ghostcmd = $opts{botghostcmd}) =~ s/%(owner|botnick)%/$opts{$1}/eg;
            sts($ghostcmd) if $ghostcmd;
            sts("NICK $primnick");
        }
    }
    if (report_threshold(600) && $pausemode) { # warn every 10m
        chanmsg("WARNING: Cannot write database in PAUSE mode!");
    }
    # do not write in pause mode, and do not write if not yet connected. (would
    # log everyone out if the bot failed to connect. $lasttime = time() on
    # successful join to $opts{botchan}, initial value is 1). if fails to open
    # $opts{dbfile}, will not update $lasttime and so should have correct values
    # on next rpcheck().
    if ($lasttime != 1) {
        my $curtime=time();
        for my $k (keys(%rps)) {
            if ($rps{$k}{online} && exists $rps{$k}{nick} &&
                $rps{$k}{nick} && exists $onchan{$rps{$k}{nick}}) {
                $rps{$k}{next} -= ($curtime - $lasttime);
                $rps{$k}{idled} += ($curtime - $lasttime);
                if ($rps{$k}{next} < 1) {
                    $rps{$k}{level}++;
		    my $ttl = int(ttl($rps{$k}{level}));
		    $rps{$k}{next} += $ttl;
                    chanmsg("$k, the $rps{$k}{class}, has attained level ".
                            "$rps{$k}{level}! Next level in ".
                            duration($rps{$k}{next}).".");
                    find_item($k);
                    challenge_opp($k);
                }
            }
            # attempt to make sure this is an actual user, and not just an
            # artifact of a bad PEVAL
        }
	if (!$pausemode && report_threshold(60)) { writedb(); }
	$oldrpreport = $rpreport;
	$rpreport += $curtime - $lasttime;
        $lasttime = $curtime;
    }
}

sub swap_items($$$) { # items will have their types automatically appended
    my ($u,$opp,$message)=@_;
    my $typeid = int(rand(@items));
    my $type = $items[$typeid];
    my $mylevel = user_item_val($u,$typeid);
    my $opplevel = user_item_val($opp,$typeid);
    if ($opplevel > $mylevel) {
	my $myitem = user_item($u,$typeid);
	my $oppitem = user_item($opp,$typeid);
	$message = rewrite_for_players($message, [$u, $opp]);
	$message = rewrite_for_items($message, $type, 
				     [item_describe($typeid,$myitem,0,1), 
				      item_describe($typeid,$oppitem,0,1)]);
	chanmsg_l($message);
	$rps{$u}{item}[$typeid] = $oppitem;
	$rps{$opp}{item}[$typeid] = $myitem;
	return undef;
    }
    return $type;
}

sub battle_result($$) {
    my ($delta,$them)=@_;
    my $phrase = 'has a blow-less standoff, considering it a victory'; # draws
    #              1       3       9        27        81          243      729     2187
    my @results=qw/chaffed bruised battered pummelled overpowered defeated crushed destroyed/;
    if($delta<0) { while($delta<=-1) { $phrase="but is ".shift(@results); $delta/=3; } }
    else       { while($delta>=1) { $phrase="and ".shift(@results)." $them"; $delta/=3; } }
    return $phrase;
}

sub simple_fight($$$$) {
    my @p=($_[0],$_[1]);
    my ($flag,$chal) = ($_[2]<=>0, $_[3]); # opp can only be primnick in a challenge fight
    my @sum = map { itemsum($_,1); } @p;
    my @roll = map { int(rand($_)); } @sum;
    my $winner = $roll[0] >= $roll[1] ? 0 : 1; # asymmetry - FIX!
    my $loser = 1-$winner; # not used much - is it worth having?
    my $changer = (0, $loser, $winner)[$flag]; # use [-1] to access final element
    my $nochange = 1-$changer; # want $p[$nochange] more often than this
    my $sign = $flag || (2*$winner-1); # 0 -> p0wins=-1, p0loses=+1
    my $gain = ($p[$nochange] eq $primnick) ? (15-5*$sign) : int($rps{$p[$nochange]}{level}/4);
    $gain = 7 if $gain < 7;
    if($p[$changer] eq $primnick) { # bot can't change, pretend nothing happened
	chanmsg_l("There's tension in the air, but nobody does anything.");
	return 0;
    }
    $gain = int(($gain/100)*$rps{$p[$changer]}{next});
    my $gainmsg = duration($gain)." is ".($sign>0?"added to":"removed from")." $p[$changer]\'s clock";
    my $them = $p[1] eq $primnick ? "them" : them($p[1]);
    chanmsg_l("$p[0] [$roll[0]/$sum[0]] has $chal $p[1] [$roll[1]/$sum[1]] ".
	      battle_result($roll[0]-$roll[1],$them)." in combat! $gainmsg.");
    $rps{$p[$changer]}{next} += $sign * $gain;
    chanmsg("$p[$changer] reaches next level in ".duration($rps{$p[$changer]}{next}).".");
    return ($roll[0]-$roll[1])/($sum[$winner]||1);
}

sub fight_with_side_effects($$$) {
    my($u,$opp,$chal) = @_; # opp can only be primnick in a challenge fight
    my $delta=simple_fight($u,$opp,0,$chal);
    if (($delta<0) or ($opp eq $primnick)) { return; }
    my $csfactor = ($chal=~m/^ch/ && $rps{$u}{alignment} eq "g") ? 50
	: ($chal=~m/^ch/ && $rps{$u}{alignment} eq "e") ? 20
	: 35;
    if (rand($csfactor) < 1) {
	my $gain = int(((5 + int(rand(20)))/100) * $rps{$opp}{next});
	chanmsg_l("$u has dealt $opp a Critical Strike! ".
		  duration($gain)." is added to $opp\'s clock.");
	$rps{$opp}{next} += $gain;
	chanmsg("$opp reaches next level in ".duration($rps{$opp}{next}).".");
    }
    elsif (rand(25) < 1 && $rps{$u}{level} > 19) {
	swap_items($u, $opp,
		   "In the fierce battle, %player1% dropped %their1% %item1%! ".
		   "%player0% picks it up, tossing %their0% old %item0% to %player1%");
    }
}

sub challenge_opp { # pit argument player against random player
    my $u = shift;
    if ($rps{$u}{level} < 25) { return unless rand(4) < 1; }
    my @opps = grep { $rps{$_}{online} } keys(%rps);
    return unless scalar(@opps)>1;
    my $opp = $opps[int(rand(@opps))];
    $opp = $primnick if ($opp eq $u);
    fight_with_side_effects($u,$opp,"challenged");
}

sub brawl($) {
    my @players = grep { $rps{$_}{online} } keys(%rps);
    return unless(scalar(@players)>=2);
    my $u = $players[int(rand(@players))];
    my $opp;
    while(($opp=$players[int(rand(@players))]) eq $u) { ; }
    simple_fight($u,$opp,$_[0],"been forced to fight");
}

sub team_battle { # pit three players against three other players
    my @opp = grep { $rps{$_}{online} } keys(%rps);
    return if @opp < 6;
    splice(@opp,int(rand(@opp)),1) while @opp > 6;
    fisher_yates_shuffle(\@opp);
    my $mysum = itemsum($opp[0],1) + itemsum($opp[1],1) + itemsum($opp[2],1);
    my $oppsum = itemsum($opp[3],1) + itemsum($opp[4],1) + itemsum($opp[5],1);
    my $gain = $rps{$opp[0]}{next};
    for my $p (1,2) {
        $gain = $rps{$opp[$p]}{next} if $gain > $rps{$opp[$p]}{next};
    }
    $gain = int($gain*.20);
    my $myroll = int(rand($mysum));
    my $opproll = int(rand($oppsum));
    if ($myroll >= $opproll) {
        chanmsg_l("$opp[0], $opp[1], and $opp[2] [$myroll/$mysum] have ".
                  "team battled $opp[3], $opp[4], and $opp[5] [$opproll/".
                  "$oppsum] and won! ".duration($gain)." is removed from ".
                  "their clocks.");
        $rps{$opp[0]}{next} -= $gain;
        $rps{$opp[1]}{next} -= $gain;
        $rps{$opp[2]}{next} -= $gain;
    }
    else {
        chanmsg_l("$opp[0], $opp[1], and $opp[2] [$myroll/$mysum] have ".
                  "team battled $opp[3], $opp[4], and $opp[5] [$opproll/".
                  "$oppsum] and lost! ".duration($gain)." is added to ".
                  "their clocks.");
        $rps{$opp[0]}{next} += $gain;
        $rps{$opp[1]}{next} += $gain;
        $rps{$opp[2]}{next} += $gain;
    }
}

sub downgrade_item { # returns the decreased item level
    my $level = $_[0];
    my ($ulevel,$tag) = ($level =~ /^(\d+)([a-z]?)/);
    if($tag) {
	my $uid = $uniques{$tag};
	$tag = '' if ($ulevel <= $uniques[$uid]{baselevel});
    }
    $ulevel-- if ($ulevel > 0);
    return "$ulevel$tag";
}

sub process_items() { # decrease items lying around
    my $curtime = time();
    while (my ($xy,$aref) = each(%mapitems)) {
	# print STDERR ("Processing ".scalar(@$aref)." items at $xy\n");
	for (my $i=0; $i<scalar(@$aref); ++$i) { # length may  change on the fly...
	    my $level = $aref->[$i]{level};
	    my $ttl = int($opts{rpitembase} * ttl(item_val($level)) / 600);
	    if ($aref->[$i]{lasttime} + $ttl <= $curtime ) {
		$aref->[$i]{lasttime} += $ttl;
		$aref->[$i]{level} = downgrade_item($level);
		if ($aref->[$i]{level} eq '0') { splice(@$aref,$i,1); $i--; } # ... here
		delete($mapitems{$xy}) if (!scalar(@$aref));
		$mapitems_dirty++;
	    }
	}
    }
}

sub drop_item($$$) { # drop item on the map
    my ($xy,$typeid,$level) = @_;
    my $ulevel = item_val($level);
    if (!$opts{rpitembase} or $ulevel <= 0) { return; }
    # if(!defined($mapitems{$xy})) { $mapitems{$xy} = []; }
    push(@{$mapitems{$xy}}, { typeid=>$typeid, level=>$level, lasttime=>time() });
    $mapitems_dirty++;
}
sub drop_user_item($$) {
    drop_item("$rps{$_[0]}{x}:$rps{$_[0]}{y}", $_[1], $rps{$_[0]}{item}[$_[1]]);
}

sub exchange_object($$$$) {
    my ($u,$typeid,$level,$suffix)=@_;
    my $notice;
    if($suffix) {
	my $uref = $uniques[$uniques{$suffix}];
	my $fortune=''; # "The light of the gods shines down upon you! "
	if($uniquemsg{$rps{$u}{alignment}}) {
	    $fortune = $uniquemsg{$rps{$u}{alignment}}.' ';
	}
	$notice = "${fortune}You have found " . 
	    item_describe($uref->{typeid},"$level$suffix",1,0) . "! $uref->{enemies}";
    }
    else {
	my $type = $items[$typeid];
	$notice = "You found ".item_describe($typeid,$level,1,1).
	    "! Your current $type is only ".item_describe($typeid,$rps{$u}{item}[$typeid],0,0).
	    ", so it seems Luck is with you!";
    }
    notice($notice,$rps{$u}{nick});
    clog($notice);
    drop_user_item($u, $typeid);
    $rps{$u}{item}[$typeid] = "$level$suffix";
}

sub find_item { # find item for argument player
    my $u = shift;
    my $level = 1;
    for my $num (1 .. int($rps{$u}{level}*1.5)) {
        if (rand(1.4**($num/4)) < 1) {
            $level = $num;
        }
    }
    for my $m (0 .. $#uniques) {
        my $uniq = $uniques[$m];
        if ($rps{$u}{level} >= $uniq->{userlevel} && rand(40) < 1) {
            my $ulevel = $uniq->{baselevel} + int(rand($uniq->{levelrange}));
            my $utypeid = $uniq->{typeid};
            if ($ulevel >= $level && $ulevel > user_item_val($u,$utypeid)) {
		exchange_object($u, $utypeid, $ulevel, $uniq->{suffix});
                return;
            }
        }
    }

    my $typeid = int(rand(@items));
    my $clevel = user_item_val($u,$typeid);
    if ($level > $clevel) {
	exchange_object($u, $typeid, $level, '');
    }
    else {
	my $type = $items[$typeid];
	notice("You found ".item_describe($typeid,$level,1,1).
	       ". Your current $type is ".item_describe($typeid,user_item($u,$typeid),0,0).
	       ", so it seems Luck is against you. You toss the $type.",
	       $rps{$u}{nick});
	# should we drop this on the map - will that clutter the map?
	# definitely not if there's no decay.
	drop_item("$rps{$u}{x}:$rps{$u}{y}", $typeid, $level) if($opts{rpitembase});
    }
}

sub loaddb { # load the players and items database
    backup();
    my $l;
    %rps = ();
    my $style=0; # 0=old, 1=new with "[ items ]"
    my $fieldcount=10;
    if (!open(RPS,$opts{dbfile}) && -e $opts{dbfile}) {
        sts("QUIT :loaddb() failed: $!");
    }
    while ($l=<RPS>) {
        chomp($l);
        # work out if it's old style or new style
        if(!$style) { 
            if($l =~ s/\[\s+([\da-z\t]*?)\s+\]\s+//) {
                my @dbitems=split(/\t/, $1);
                $fieldcount=@dbitems;
                debug("INFO: new style with $fieldcount items 0..$#dbitems");
                if($fieldcount != @items) {
                    debug("ERROR: db's items 0..$#dbitems differs from our 0..$#items");
                }
                $style=1;
            }
        }
        next if $l =~ /^#/; # skip comments

        my @dbitems;
        my @i;
        my $err;
        if($style == 1) {
            if($l !~ s/\[\s+([\da-z\t]*?)\s+\]\s+//) {
                $err = "QUIT: Anomaly in loaddb(); line $. of $opts{dbfile} has missing [] section";
                goto bail_loaddb;
            }
            @dbitems = split("\t", $1);
            if(@dbitems != $fieldcount) {
                $err = "QUIT: Anomaly in loaddb(); line $. of $opts{dbfile} wrong [$fieldcount] section = '$1'";
                goto bail_loaddb;
            }
            @i = split("\t", $l);
            if(@i != 23) { # was 33 when we had 10 items
                $err = "QUIT: Anomaly in loaddb(); line $. of $opts{dbfile} wrong default section";
                goto bail_loaddb;
            }
        } else {
            @i = split("\t",$l);
            if(@i == 32) { push(@i, "u"); }
            elsif (@i != 33) { 
                $err = "QUIT: Anomaly in loaddb(); line $. of $opts{dbfile} has ".
                    "wrong fields (".scalar(@i).")";
                goto bail_loaddb;
            }
            @dbitems = splice(@i,21,10);
        }

        # Now we have the item fields and the other fields separated from
        # each other, we can stick them in our internal hash.
        if (!$sock) { # if not RELOADDB
            if ($i[8]) { $prev_online{$i[7]}=$i[0]; $i[8]=0; } # log back in
        }
        ($rps{$i[0]}{pass},
        $rps{$i[0]}{isadmin},
        $rps{$i[0]}{level},
        $rps{$i[0]}{class},
        $rps{$i[0]}{next},
        $rps{$i[0]}{nick},
        $rps{$i[0]}{userhost},
        $rps{$i[0]}{online},
        $rps{$i[0]}{idled},
        $rps{$i[0]}{x},
        $rps{$i[0]}{y},
        $rps{$i[0]}{pen_mesg},
        $rps{$i[0]}{pen_nick},
        $rps{$i[0]}{pen_part},
        $rps{$i[0]}{pen_kick},
        $rps{$i[0]}{pen_quit},
        $rps{$i[0]}{pen_quest},
        $rps{$i[0]}{pen_logout},
        $rps{$i[0]}{created},
        $rps{$i[0]}{lastlogin},
        $rps{$i[0]}{alignment},
        $rps{$i[0]}{gender}) = @i[1..22];

        # @dbitems may be too long or too short. if too long, they're 
        # remembered until the next save, and then not written out.
        # if too short (new items have appeared), then undef stands in
        # for 0, and hopefully the warnings aren't too noisy.
        $rps{$i[0]}{item} = [splice(@dbitems,0,@items)];
        next;

bail_loaddb:
        sts($err);
        debug($err,1);
    }
    close(RPS);
    debug("loaddb(): loaded ".scalar(keys(%rps))." accounts, ".
          scalar(keys(%prev_online))." previously online.");

    return if (!$opts{itemdbfile});
    %mapitems = ();
    $mapitems_dirty=0;
    if(! -e $opts{itemdbfile}) {
	debug("loaddb(): no items file to load, that's easy.");
	return;
    }
    if (!open(ITEMS,$opts{itemdbfile})) {
	if (-e $opts{itemdbfile}) { sts("QUIT :loaddb() failed ($opts{itemdbfile}): $!"); }
	return;
    }
    my $cnt = 0;
    my $curtime = time();
    while ($l=<ITEMS>) {
	chomp($l);
	next if $l =~ /^#/; # skip comments
	my @i = split("\t",$l);
	if (@i != 4) {
	    my $debug="Anomaly in loaddb(); line $. of $opts{itemdbfile} has wrong ".
		"fields (".scalar(@i).")";
	    sts("QUIT: $debug");
	    debug($debug,1);
	}
	push(@{$mapitems{$i[0]}}, { typeid=>$i[1], level=>$i[2], lasttime=>$curtime-$i[3] });
	$cnt++;
    }
    close(ITEMS);
    debug("loaddb(): loaded $cnt items.");
}

sub movesomeplayers(@) {
    my @temp=@_;
    my %positions = ();
    my $numtomove=scalar(@temp);
    while(@temp) {
	my $player=splice(@temp,rand(scalar(@temp)),1);
        $rps{$player}{x} += int(rand(3))-1;
        $rps{$player}{y} += int(rand(3))-1;
        # if player goes over edge, wrap them back around
        if ($rps{$player}{x} >= $opts{mapx}) { $rps{$player}{x} = 0; }
        if ($rps{$player}{y} >= $opts{mapy}) { $rps{$player}{y} = 0; }
        if ($rps{$player}{x} < 0) { $rps{$player}{x} = $opts{mapx}-1; }
        if ($rps{$player}{y} < 0) { $rps{$player}{y} = $opts{mapy}-1; }

        if (exists($positions{$rps{$player}{x}}{$rps{$player}{y}}) &&
            !$positions{$rps{$player}{x}}{$rps{$player}{y}}{battled}) {
            if ($rps{$positions{$rps{$player}{x}}{$rps{$player}{y}}{user}}{isadmin} &&
                !$rps{$player}{isadmin} && rand(100) < 1) {
                chanmsg("$player encounters ".
                        $positions{$rps{$player}{x}}{$rps{$player}{y}}{user}.
                        " and bows humbly.");
            }
            if (rand($numtomove) < 1) {
                $positions{$rps{$player}{x}}{$rps{$player}{y}}{battled}=1;
                collision_fight($player,
                                $positions{$rps{$player}{x}}{$rps{$player}{y}}{user});
            }
        }
        else {
            $positions{$rps{$player}{x}}{$rps{$player}{y}}{battled}=0;
            $positions{$rps{$player}{x}}{$rps{$player}{y}}{user}=$player;
        }
    }
}

sub moveplayers {
    return unless $lasttime > 1;
    my @online = grep { $rps{$_}{online} } keys %rps;
    my $onlinecount = scalar(@online);
    return unless $onlinecount;
    for (my $i=0;$i<$opts{self_clock};++$i) {
        # temporary hash to hold player positions, detect collisions
        my @questers = ();
        if ($quest{type} == 2 && (@questers = @{$quest{questers}})) {
            my $allgo = 1; # have all users reached <p1|p2>?
            my ($x,$y) = @{$quest{"p$quest{stage}"}};
            for (@questers) {
                if ($rps{$_}{x} != $x || $rps{$_}{y} != $y) { $allgo=0; last; }
            }
            # all participants have reached point 1, now point 2
            if ($quest{stage}==1 && $allgo) {
                $quest{stage}=2;
                writequestfile();
            }
            elsif ($quest{stage} == 2 && $allgo) {
                chanmsg_l(comma_list(\@questers)." have completed their ".
                          "journey! 25% of their burden is eliminated.");
                for (@questers) {
                    $rps{$_}{next} = int($rps{$_}{next} * .75);
                }
                undef(@{$quest{questers}});
                $quest{qtime} = time() + 21600; # next quest starts in 6 hours
                $quest{type} = 1; # probably not needed
                writequestfile();
            }
            else {
                for (@questers) {
                    if (rand(100) < 1) {
                        my ($dx,$dy) = ($x-$rps{$_}{x}, $y-$rps{$_}{y});
                        if(rand(abs($dy))<abs($dx)) {
                            $rps{$_}{x} += ($x <=> $rps{$_}{x});
                        }
                        if(rand(abs($dx))<abs($dy)) {
                            $rps{$_}{y} += ($y <=> $rps{$_}{y});
                        }
                    }
                }
            }

            # Always move other players indepenently of what questers are doing
            my %temp;
            # load keys of %temp with online users
            ++@temp{@online};
            # delete questers from list
            delete(@temp{@questers});
            movesomeplayers(keys(%temp));
        }
        else {
            movesomeplayers(@online);
        }
	# pick up items lying around, priority amongst players is semi-random
	# it depends on the order of hash traversal, which can change when the
	# hash changes.
	next if (!$opts{rpitembase});
	for my $u (keys(%rps)) {
	    next unless $rps{$u}{online};
	    my $x = $rps{$u}{x};
	    my $y = $rps{$u}{y};
	    next unless exists($mapitems{"$x:$y"});
	    for (my $i=0; $i<=$#{$mapitems{"$x:$y"}}; ++$i) {
		my $item = $mapitems{"$x:$y"}[$i];
		my ($val,$tag) = ($item->{level} =~ /^(\d+)([a-z]?)$/);
		if ($val > user_item_val($u, $item->{typeid})) {
		    exchange_object($u, $item->{typeid}, $val, $tag);
		    splice(@{$mapitems{"$x:$y"}},$i,1);
		    $mapitems_dirty++;
		    --$i; # everything's shifted up by one
		}
	    }
	}
    }
}

sub mksalt { # generate a random salt for passwds
    join '',('a'..'z','A'..'Z','0'..'9','/','.')[rand(64), rand(64)];
}

sub chanmsg { # send a message to the channel
    my $msg = shift or return undef;
    if ($silentmode & 1) { return undef; }
    privmsg($msg, $opts{botchan}, shift);
}

sub chanmsg_l { # log to mod log, and send to chan
    my $msg = shift or return undef;
    clog($msg);
    chanmsg($msg);
}

sub privmsg { # send a message to an arbitrary entity
    my $msg = shift or return undef;
    my $target = shift or return undef;
    my $force = shift;
    if (($silentmode == 3 || ($target !~ /^[\+\&\#]/ && $silentmode == 2))
        && !$force) {
        return undef;
    }
    while (length($msg)) {
        sts("PRIVMSG $target :".substr($msg,0,450),$force);
        substr($msg,0,450)="";
    }
}

sub notice { # send a notice to an arbitrary entity
    my $msg = shift or return undef;
    my $target = shift or return undef;
    my $force = shift;
    if (($silentmode == 3 || ($target !~ /^[\+\&\#]/ && $silentmode == 2))
        && !$force) {
        return undef;
    }
    while (length($msg)) {
        sts("NOTICE $target :".substr($msg,0,450),$force);
        substr($msg,0,450)="";
    }
}

sub help { # print help message
    (my $prog = $0) =~ s/^.*\///;

    print "
usage: $prog [OPTIONS]
  --help, -h           Print this message
  --verbose, -v        Print verbose messages
  --server, -s         Specify IRC server:port to connect to
  --botnick, -n        Bot's IRC nick
  --botuser, -u        Bot's username
  --botrlnm, -r        Bot's real name
  --botchan, -c        IRC channel to join
  --botident, -p       Specify identify-to-services command
  --botmodes, -m       Specify usermodes for the bot to set upon connect
  --botopcmd, -o       Specify command to send to server on successful connect
  --botghostcmd, -g    Specify command to send to server to regain primary
                       nickname when in use
  --doban              Advertisement ban on/off flag
  --okurl, -k          Bot will not ban for web addresses that contain these
                       strings
  --debug              Debug on/off flag
  --helpurl            URL to refer new users to
  --admincommurl       URL to refer admins to

  Timing parameters:
  --rpbase             Base time to level up
  --rpstep             Time to next level = rpbase * (rpstep ** CURRENT_LEVEL)
  --rpitembase         Base time for lifetime of dropped items
  --rppenstep          PENALTY_SECS=(PENALTY*(RPPENSTEP**CURRENT_LEVEL))
";
# missing:
# software:     --checkupdates,
# network:      --localaddr, --reconnect, --reconnect_wait
# commands:     --statuscmd, --allowuserinfo, 
# players:      --casematters, --noccodes, --nononp,
# irc_settings: --owner, --detectsplits, --splitwait, 
# irc_features: --modesperline, --senduserlist, --voiceonlogin
# theme:        --itemsfile, --eventsfile, 
# database:     --dbfile, --itemdbfile, --questfilename
# logging:      --debugfile, --modsfile, 
# map:          --mapx, --mapy, --mapurl,
# game:         --noscale, --self_clock, --top_period, --chal_period
# penalties:    --limitpen,
# daemon:       --daemonize, --pidfile,
# --phonehome
}

sub itemsum {
    my $user = shift;
    # is this for a battle? if so, good users get a 10% boost and evil users get
    # a 10% detriment
    my $battle = shift;
    return -1 unless defined $user;
    my $sum = 0;
    if ($user eq $primnick) {
        for my $u (keys(%rps)) {
	    my $usum = itemsum($u);
	    $sum = $usum if ($sum < $usum);
        }
        return $sum+1;
    }
    if (!exists($rps{$user})) { return -1; }
    $sum += user_item_val($user,$_) for (0..$#items);
    if ($battle) {
        return $rps{$user}{alignment} eq 'e' ? int($sum*.9) :
               $rps{$user}{alignment} eq 'g' ? int($sum*1.1) :
               $sum;
    }
    return $sum;
}

sub daemonize() {
    # win32 doesn't daemonize (this way?)
    if ($^O eq "MSWin32") {
        print debug("Nevermind, this is Win32, no I'm not.")."\n";
        return;
    }
    use POSIX 'setsid';
    $SIG{CHLD} = sub { };
    fork() && exit(0); # kill parent
    POSIX::setsid() || debug("POSIX::setsid() failed: $!",1);
    $SIG{CHLD} = sub { };
    fork() && exit(0); # kill the parent as the process group leader
    $SIG{CHLD} = sub { };
    open(STDIN,'/dev/null') || debug("Cannot read /dev/null: $!",1);
    open(STDOUT,'>/dev/null') || debug("Cannot write to /dev/null: $!",1);
    open(STDERR,'>/dev/null') || debug("Cannot write to /dev/null: $!",1);
    # write our PID to $opts{pidfile}, or return semi-silently on failure
    open(PIDFILE,">$opts{pidfile}") || do {
        debug("Error: failed opening pid file: $!");
        return;
    };
    print PIDFILE $$;
    close(PIDFILE);
}

sub rewrite_for_items($$$) {
    my ($s,$t,$ts)=@_;
    $s =~ s/%item([01]?)%/$ts->[int("0$1")]/g;
    $s =~ s/%type%/$t/g;
    return $s;
}
sub rewrite_for_players($$) {
    my ($s,$p)=@_;
    $s =~ s/%player([01]?)%/$p->[int("0$1")]/g;
    $s =~ s/%level([01]?)%/$rps{$p->[int("0$1")]}{level}/g;
    $s =~ s/%players%/comma_list($p)/eg;
    $s =~ s/%(he|she|they)([01]?)%/they($p->[int("0$2")])/eg;
    $s =~ s/%(his|her|their)([01]?)%/their($p->[int("0$2")])/eg;
    $s =~ s/%(him|her|them)([01]?)%/them($p->[int("0$2")])/eg; # her is impossible here
    $s =~ s/%(is|are)([01]?)%/are($p->[int("0$2")])/eg;
    $s =~ s/%(was|were)([01]?)%/were($p->[int("0$2")])/eg;
    $s =~ s/%(has|have)([01]?)%/have($p->[int("0$2")])/eg;
    #$s =~ s/%(verb|verbs)([01]?)%/verb($p->[int("0$2")])/eg;
    return $s;
}
sub rewrite_programatics($$) {
    my ($s,$r)=@_;
    while($s =~ m/.*%{(.*?)}%/) { # work from inside out - don't worrry about .* complexity
	my ($start, $end)=($-[1]-2, $+[1]+2);
        my $len=$end-$start;
        if(index($1,'|')>=0 or index($1,'#')<0) {
            my @list=split(/\|/, $1);
            substr($s,$start,$len) = $list[int(rand(@list))];
        } elsif($1 =~ m/^([\d.]+)\#(?:([-+])([\d.]+))?\#([\d.]+)$/) {
            my $step = $3 ? $3 * ($2 eq '-'?-1:1) : 1;
            my $numsteps = int(($4-$1)/$step)+1;
            substr($s,$start,$len) = $1+int($r*$numsteps)*$step;
        } else {
            debug("No choice in macro ". substr($s,$start,$len));
            substr($s,$start,$len) = substr($s,$start+2,$len-4);
        }
    }
    return $s;
}

sub rewrite_event($$$) {
    my ($s,$p,$r)=@_;
    $s=rewrite_for_players($s,$p);
    $s=rewrite_programatics($s,$r);
    return $s;
}

sub modify_item($) {
    my $good = ($_[0] > 0);
    my @players = grep { $rps{$_}{online} } keys(%rps);
    return unless @players;
    my $player = $players[rand(@players)];
    if (@fragileitems and rand(10) < 1) {
	my @change = ('loses', 'gains');
        my($typeid,$change);
        while(!$change) {
            $typeid = $fragileitems[rand(@fragileitems)];
            $change = ($good ? $godsend[$typeid] : $calamity[$typeid]);
        }
        $change = rewrite_event($change, [$player], undef); # random number not used currently
        my $type = $items[$typeid];
        my $suffix="";
        if ($rps{$player}{item}[$typeid] =~ /^(\d+)(\D)$/) { $suffix=$2; $type=item_describe($typeid,"$1$2",0,1); }
        $change = "${player}$change" .
            " $player\'s $type $change[$good] 10% of its effectiveness.";
        chanmsg_l($change);

        $rps{$player}{item}[$typeid] = int(user_item_val($player,$typeid) * (1+$_[0]*.1));
        $rps{$player}{item}[$typeid].=$suffix;
    }
    else {
	my @timechange = ('terrible calamity has slowed',
			  'wondrous godsend has accelerated');
        my $rand = rand();
        my $time = int(int(5 + $rand*8) / 100 * $rps{$player}{next});
        my $actioned = get_event($good?'G':'C', [$player], $rand);
        chanmsg_l("$player".(' 'x(substr($actioned,0,3)ne"'s "))."$actioned. ".
                  "This $timechange[$good] ".them($player)." ".
                  duration($time)." $tofrom[$good] level ".
                  ($rps{$player}{level}+1).".");
        $rps{$player}{next} -= $time * ($_[0] <=> 0);
        chanmsg("$player reaches next level in ".duration($rps{$player}{next}).
                ".");
    }
}

sub calamity { modify_item(-1); }  # suffer a little one
sub godsend { modify_item(+1); } # bless the unworthy

sub quest {
    my @questers = grep { $rps{$_}{online} && $rps{$_}{level} > 39 &&
                              time()-$rps{$_}{lastlogin}>36000 } keys(%rps);
    if (@questers < 4) { return undef; }
    while (@questers > 4) {
        splice(@questers,int(rand(@questers)),1);
    }
    %quest = %{get_quest()};
    $quest{questers} = \@questers;
    my $questtext=get_event('QI', \@questers, undef);
    $questtext =~ s/%quest%/$quest{text}/; # only expect one, more is noise
    $quest{text} = rewrite_programatics($questtext,undef);
    if ($quest{type} == 1) {
        $quest{qtime} = time()+43200+int(rand(43201));
        chanmsg("$quest{text} Quest to end in ".duration($quest{qtime}-time()).".");
    }
    elsif ($quest{type} == 2) {
        chanmsg("$quest{text} Participants must first reach [$quest{p1}->[0],".
                "$quest{p1}->[1]], then [$quest{p2}->[0],$quest{p2}->[1]].".
                ($opts{mapurl}?" See $opts{mapurl} to monitor their journey's ".
                "progress.":""));
    }
    writequestfile();
}

sub questpencheck {
    my $k = shift;
    my ($quester,$player);
    for $quester (@{$quest{questers}}) {
        if ($quester eq $k) {
            chanmsg_l(get_event('QF', [$quester], undef));
            for $player (grep { $rps{$_}{online} } keys %rps) {
                my $gain = int(15 * ($opts{rppenstep}**$rps{$player}{level}));
                $rps{$player}{pen_quest} += $gain;
                $rps{$player}{next} += $gain;
            }
            undef(@{$quest{questers}});
            $quest{qtime} = time() + 43200; # 12 hours
        }
    }
}

sub flog($$) {
    my ($file,$mesg) = @_;
    open(B,">>$file") or do {
        debug("Error: Cannot open $file}: $!");
        chanmsg("Error: Cannot open $file}: $!");
        return $mesg;
    };
    print B ts()."$mesg\n";
    close(B);
    return $mesg;
}
sub clog($) {
    flog($opts{modsfile}, shift);
}
my $debug_reentrancy = 0;
sub debug {
    my ($text, $die) = @_;
    return if ($debug_reentrancy > 0);
    $debug_reentrancy++;
    $text =~ s/[\r\n]//g;
    flog($opts{debugfile}, $text) if ($opts{debug} || $opts{verbose});
    if ($die) { die("$text\n"); }
    $debug_reentrancy--;
    return $text;
}

sub backup() {
    if (! -d ".dbbackup/") { mkdir(".dbbackup",0700); }
    if ($^O ne "MSWin32") {
        system("cp $opts{dbfile} .dbbackup/$opts{dbfile}".time());
	system("cp $opts{itemdbfile} .dbbackup/$opts{itemdbfile}".time())
	    if(exists($opts{itemdbfile}) and -e $opts{itemdbfile});
    }
    else {
        system("copy $opts{dbfile} .dbbackup\\$opts{dbfile}".time());
	system("copy $opts{itemdbfile} .dbbackup\\$opts{itemdbfile}".time())
	    if(exists($opts{itemdbfile}) and -e $opts{itemdbfile});
    }
}

sub penalize {
    my %why = (quit=>['pen_quit',20,undef], part=>['pen_part',200,undef], # don't msg goners
	       kick=>['pen_kick',250,'being kicked'], logout=>['pen_logout',20,'logging out'],
	       privmsg=>['pen_mesg',undef,'privmsg'], notice=>['pen_mesg',undef,'notice'],
	       nick=>['pen_nick',30,'nick change'],);

    my $username = shift;
    return 0 if !defined($username);
    return 0 if !exists($rps{$username});
    my $type = shift;
    questpencheck($username);
    my ($pentype,$pen,$why) = @{$why{$type}};
    if ($type =~ m/^(?:quit|part|kick|logout)$/) {
        $rps{$username}{online}=0;
    }
    elsif ($type eq "nick") {
        my $newnick = shift;
        $rps{$username}{nick} = substr($newnick,1);
	$rps{$username}{userhost} =~ s/^[^!]+/$rps{$username}{nick}/;
    }
    elsif ($type eq "privmsg" || $type eq "notice") {
        $pen = shift(@_);
    }
    $pen = int($pen * ($opts{rppenstep}**$rps{$username}{level}));
    if ($opts{limitpen} && $pen > $opts{limitpen}) {
        $pen = $opts{limitpen};
    }
    #debug("penalize($username,$type) -> why=$why, pen=$pen, pentype=$pentype",0);
    $rps{$username}{$pentype}+=$pen;
    $rps{$username}{next} += $pen;
    notice("Penalty of ".duration($pen)." added to your timer for $why.",
           $rps{$username}{nick}) if(defined($why));
    return 1; # successfully penalized a user! woohoo!
}

sub finduser {
    my $nick = shift;
    return undef if !defined($nick);
    for my $user (keys(%rps)) {
        next unless $rps{$user}{online};
        if ($rps{$user}{nick} eq $nick) { return $user; }
    }
    return undef;
}

sub ha { # return 0/1 if username has access
    my $user = shift;
    if (!defined($user) || !exists($rps{$user})) {
        debug('Error: Attempted ha() for invalid username "'.($user//'(undef)').'"');
        return 0;
    }
    return $rps{$user}{isadmin};
}

sub checksplits { # removed expired split hosts from the hash
    my $host;
    while ($host = each(%split)) {
        if (time()-$split{$host}{time} > $opts{splitwait}) {
            $rps{$split{$host}{account}}{online} = 0;
            delete($split{$host});
        }
    }
}

sub collision_fight($$$) { fight_with_side_effects($_[0], $_[1], "come upon"); }

sub restorequest {
    my %questdef = (
                    questers => [],
                    p1 => [], # point 1 for q2
                    p2 => [], # point 2 for q2
                    qtime => time() + int(rand(21600)), # first quest starts in <=6 hours
                    text => "",
                    type => 1,
                    stage => 1); # quest info
    return %questdef unless ($opts{questfilename} and open(QF, "<$opts{questfilename}"));
    my $type;
    while(<QF>) {
        if(m/^T (.*?)\s*$/) { $questdef{text} = $1; }
        elsif(m/^Y ([12])\s*$/) { $type = $questdef{type} = int($1); }
        elsif(m/^S (\d+)\s*$/) { $questdef{$type==1?'qtime':'stage'} = int($1); }
        elsif($type==2 and m/^P (\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s*$/) 
        { $questdef{p1}=[$1,$2]; $questdef{p2}=[$3,$4]; }
        elsif(m/^P(\d) (\S+)/) { $questdef{questers}->[$1-1] = $2; }
        else { debug("Unknown line in questfile $opts{questfilename}: $_"); }
    }
    close(QF);
    my $lack=join('',map{defined($questdef{questers}->[$_])?'':$_}(0..3));
    if(length($lack)) { debug("Lacking questers: $lack in questfile $opts{questfilename}:"); }
    return %questdef;
}

sub writequestfile {
    return unless $opts{questfilename};
    open(QF,">$opts{questfilename}") or do {
        chanmsg("Error: Cannot open $opts{questfilename}: $!");
        return;
    };
    # if no active quest, just empty questfile. otherwise, write it
    if (@{$quest{questers}}) {
        if ($quest{type}==1) {
            print QF "T $quest{text}\n".
                     "Y 1\n".
                     "S $quest{qtime}\n".
                     "P1 $quest{questers}->[0]\n".
                     "P2 $quest{questers}->[1]\n".
                     "P3 $quest{questers}->[2]\n".
                     "P4 $quest{questers}->[3]\n";
        }
        elsif ($quest{type}==2) {
            print QF "T $quest{text}\n".
                     "Y 2\n".
                     "S $quest{stage}\n".
                     "P $quest{p1}->[0] $quest{p1}->[1] $quest{p2}->[0] ".
                        "$quest{p2}->[1]\n".
                     "P1 $quest{questers}->[0] $rps{$quest{questers}->[0]}{x} ".
                         "$rps{$quest{questers}->[0]}{y}\n".
                     "P2 $quest{questers}->[1] $rps{$quest{questers}->[1]}{x} ".
                         "$rps{$quest{questers}->[1]}{y}\n".
                     "P3 $quest{questers}->[2] $rps{$quest{questers}->[2]}{x} ".
                         "$rps{$quest{questers}->[2]}{y}\n".
                     "P4 $quest{questers}->[3] $rps{$quest{questers}->[3]}{x} ".
                         "$rps{$quest{questers}->[3]}{y}\n";
        }
    }
    close(QF);
}

sub holiness {
    my @players = grep { $rps{$_}{alignment} eq "g" &&
                         $rps{$_}{online} } keys(%rps);
    return unless @players > 1;
    splice(@players,int(rand(@players)),1) while @players > 2;
    my $gain = 5 + int(rand(8));
    my $holiness=get_event('H', \@players, undef);
    $holiness =~ s/%gain%/$gain/g;
    chanmsg_l($holiness);
    $rps{$players[0]}{next} = int($rps{$players[0]}{next}*(1 - ($gain/100)));
    $rps{$players[1]}{next} = int($rps{$players[1]}{next}*(1 - ($gain/100)));
    chanmsg("$players[0] reaches next level in ".
            duration($rps{$players[0]}{next}).".");
    chanmsg("$players[1] reaches next level in ".
            duration($rps{$players[1]}{next}).".");
}

sub evilness {
    my @evil = grep { $rps{$_}{alignment} eq "e" &&
                      $rps{$_}{online} } keys(%rps);
    return unless @evil;
    my $me = $evil[rand(@evil)];
    if (int(rand(2)) < 1) {
        # evil only steals from good :^(
        my @good = grep { $rps{$_}{alignment} eq "g" &&
                          $rps{$_}{online} } keys(%rps);
        return unless @good;
        my $target = $good[rand(@good)];
	my $didntswap =
	    swap_items($me, $target,
		       "%player0% stole %player1%\'s %item1% ".
		       "while %they1% %were1% sleeping! ".
		       "%player0% leaves %their0% old %item0% behind, ".
		       "which %player1% then takes.",
		       );
	if($didntswap) {
            notice("You made to steal $target\'s $didntswap, but realized it was ".
                   "lower level than your own. You creep back into the ".
                   "shadows.",$rps{$me}{nick});
        }
    }
    else { # being evil only pays about half of the time...
        my $gain = 1 + int(rand(5));
	my $duration = duration(int($rps{$me}{next} * ($gain/100)));
	my $evilness=get_event('E',[$me],undef);
	$evilness =~ s/%duration%/$duration/g;
	chanmsg_l($evilness);
        $rps{$me}{next} = int($rps{$me}{next} * (1 + ($gain/100)));
        chanmsg("$me reaches next level in ".duration($rps{$me}{next}).".");
    }
}

sub fisher_yates_shuffle {
    my $array = shift;
    my $i;
    for ($i = @$array; --$i; ) {
        my $j = int rand ($i+1);
        next if $i == $j;
        @$array[$i,$j] = @$array[$j,$i];
    }
}

sub writedb {
    open(RPS,">$opts{dbfile}") or do {
        chanmsg("ERROR: Cannot write $opts{dbfile}: $!");
        return 0;
    };
    print RPS join("\t","# username",
                        "pass",
                        "is admin",
                        "level",
                        "class",
                        "next ttl",
                        "nick",
                        "userhost",
                        "online",
                        "idled",
                        "x pos",
                        "y pos",
                        "pen_mesg",
                        "pen_nick",
                        "pen_part",
                        "pen_kick",
                        "pen_quit",
                        "pen_quest",
                        "pen_logout",
                        "created",
                        "last login",
                   "[",
                   (map { "item$_"; } (0..$#items)),
                   "]",
                        "alignment",
                        "gender")."\n";
    my $k;
    keys(%rps); # reset internal pointer
    while ($k=each(%rps)) {
        if (exists($rps{$k}{next}) && defined($rps{$k}{next})) {
            print RPS join("\t",$k,
                                $rps{$k}{pass},
                                $rps{$k}{isadmin},
                                $rps{$k}{level},
                                $rps{$k}{class},
                                $rps{$k}{next},
                                $rps{$k}{nick},
                                $rps{$k}{userhost},
                                $rps{$k}{online},
                                $rps{$k}{idled},
                                $rps{$k}{x},
                                $rps{$k}{y},
                                $rps{$k}{pen_mesg},
                                $rps{$k}{pen_nick},
                                $rps{$k}{pen_part},
                                $rps{$k}{pen_kick},
                                $rps{$k}{pen_quit},
                                $rps{$k}{pen_quest},
                                $rps{$k}{pen_logout},
                                $rps{$k}{created},
                                $rps{$k}{lastlogin},
                           "[",
                           @{$rps{$k}{item}},
                           "]",
                                $rps{$k}{alignment},
                                $rps{$k}{gender})."\n";
        }
    }
    close(RPS);

    return if(!$opts{itemdbfile});
    return if(!$mapitems_dirty);
    open(ITEMS,">$opts{itemdbfile}") or do {
	chanmsg("ERROR: Cannot write $opts{itemdbfile}: $!");
	return;
    };
    print ITEMS join("\t", "# x:y",
		     "type",
		     "level",
		     "age")."\n";
    my $curtime = time();
    my $cnt=0;
    while(my ($xy, $aref) = each(%mapitems)) {
	foreach my $i (@$aref) {
	    print ITEMS join("\t", $xy,
			     $i->{typeid},
			     $i->{level},
			     $curtime-$i->{lasttime})."\n";
	    ++$cnt;
	}
    }
    close(ITEMS);
    if(!$cnt) {
	unlink($opts{itemdbfile})
	    or chanmsg("ERROR: Cannot nuke items file");
    }
    $mapitems_dirty=0;
}

sub readconfig {
    if (! -e $conffile) {
        debug("Error: Cannot find $conffile. Copy it to this directory, ".
              "please.",1);
    }
    else {
        open(CONF,"<$conffile") or do {
            debug("Failed to open config file $conffile: $!",1);
        };
        my($line);
        while ($line=<CONF>) {
            next() if $line =~ /^#/; # skip comments
            $line =~ s/[\r\n]//g;
            $line =~ s/^\s+//g;
            next() if !length($line); # skip blank lines
            my ($key,$val) = split(/\s+/,$line,2);
            $key = lc($key);
	    $val//='';
            if (lc($val) eq "on" || lc($val) eq "yes") { $val = 1; }
            elsif (lc($val) eq "off" || lc($val) eq "no") { $val = 0; }
            if ($key eq "die") {
                die("Please edit the file $conffile to setup your bot's ".
                    "options. Also, read the README file if you haven't ".
                    "yet.\n");
            }
            elsif ($key eq "server") { push(@{$opts{servers}},$val); }
            elsif ($key eq "okurl") { push(@{$opts{okurl}},$val); }
            else { $opts{$key} = $val; }
        }
        close(CONF);
	if(!$opts{itemdbfile} and $opts{rpitembase}) {
	    debug("Without an itemdbfile, no objects will be dropped, blanking rpitembase");
	    delete($opts{rpitembase});
	}
    }
}

sub read_events {
    if (!open(Q,$opts{eventsfile})) {
        return chanmsg("ERROR: Failed to open $opts{eventsfile}: $!");
    }
    @quests = ();
    %events = (G=>[], C=>[], W=>[], L=>[], H=>[], E=>[],
	       QI=>[], QS=>[], QF=>[],
	       P=>[], PG=>[], PN=>[], PE=>[], PA=>[]);
    while (my $line = <Q>) {
        if ($line =~ /^([GCWLHE]|Q[ISF]|P[AGNE]?)\s+(.*)/) { push(@{$events{$1}}, $2); }
        elsif ($line =~ /^Q1 (.*)/) {
            push(@quests, { type=>1, text=>$1 });
        }
        elsif ($line =~ /^Q2 (\d+) (\d+) (\d+) (\d+) (.*)/) {
            push(@quests,
                 { type=>2, text=>$5, stage=>1, p1=>[$1,$2], p2=>[$3,$4] });
        }
	elsif ($line =~ /^U([GNE]?) (.*)/) {
	    if($1) { $uniquemsg{lc($1)} = $2; }
	    else { $uniquemsg{g} = $uniquemsg{n} = $uniquemsg{e} = $2; }
	}
        else { debug("Event in $opts{eventsfile} unknown: $line",0); }
    }
    close(Q);
    debug("Read ".@{$events{G}}." godsends, ".@{$events{C}}." calamaties, ".
          @{$events{W}}." HOG wins, ".@{$events{L}}." HOG losses, ".
	  @{$events{H}}." holinesses, ".@{$events{E}}." evilnesses, ".
	  @{$events{PG}}." good, ".@{$events{PN}}." neutral, ".
	  @{$events{PE}}." evil, and ".@{$events{PA}}." universal penances, ".
	  " and ".@quests." quests (with ".@{$events{QF}}." intros, ".@{$events{QF}}.
	  " failures, and ".@{$events{QS}}." sucesses).",0);
    # Must be at least one HOG win and lose line
    if(!@{$events{W}}) { push(@{$events{W}},"Weird stuff happened, pushing %player%"); }
    if(!@{$events{L}}) { push(@{$events{L}},"Weird stuff happened, pulling %player%"); }
    if(!@{$events{H}}) { push(@{$events{H}},"By cooperating, %player0% and %player1% advance %gain%\% towards their next level"); }
    if(!@{$events{E}}) { push(@{$events{E}},"%player%'s misdeeds have caught up with %him%. %duration% is added to %their% clock."); }
    if(!@{$events{QI}}) { push(@{$events{QI}},"%players% have begun a quest to %quest%, for the good of the realm."); }
    if(!@{$events{QS}}) { push(@{$events{QS}},"%players% have enriched the realm by completing their quest! 25% of their burden is eliminated."); }
    if(!@{$events{QF}}) { push(@{$events{QF}},"%player%'s selfishness sullies the task %he% and %his% fellow questers were charged with, which brings a great shame upon all the land. You are all punished for %his% transgression."); }
    if($events{'PA'} and scalar(@{$events{PA}})) {
	foreach (qw{PG PN PE}) { push(@{$events{$_}}, @{$events{PA}}); };
	delete($events{PA});
    }
    if(!@{$events{PG}}) { push(@{$events{PG}},"%player% realises that %he% %is% doing something terribly wrong with %his% life, and desires to take a step back start again."); }
    if(!@{$events{PN}}) { push(@{$events{PN}},"%player% realises that %he% %has% lost %his% way, and needs to take a step back and start again."); }
    if(!@{$events{PE}}) { push(@{$events{PE}},"%player% realises that %he% %has% wasted too much of %his% time doing frivolous things, and needs to take a step back and start again."); }
    if(!@{$events{P}}) { push(@{$events{P}},"%player% returns to restart level %level% with a clean slate."); }
}

sub get_event($$$) {
    my $evsref = $events{$_[0]};
    return rewrite_event($evsref->[int(rand(@$evsref))], $_[1], $_[2]);
}
sub get_quest($) {
    return $quests[int(rand(scalar(@quests)))];    
}

sub read_items {
    my $fn = $opts{itemsfile} || 'items.txt';
    if(!-e $fn) {
        debug("Error: items file $fn not found, please fix",1);
    }
    open(IF,"<$fn") or do {
        debug("Failed to open items file $fn: $!",1);
    };
    @items=@levels=@calamity=@godsend=@uniques=@fragileitems = ();
    %uniques=();
    my ($got, $ngot, $gotu)=(0,0,0);
    my ($line,$ix,$key,$val);
    while($line=<IF>) {
        next if $line =~ /^#/; # skip comments
        $line =~ s/^\s+//g;
        my $context;
        if($line =~ s/^item(\d):\s*//) {
            my $typeid=int($1);
            if($got>>$typeid & 1 and $line =~ m/n=/) {
                debug("Already have item$typeid = $items[$typeid]",1);
            }
            my $corg=0;
            while($line =~ s/([ncg])="([^\"]*)"\s+// or
                  $line =~ s/([ncg])=(\w+)\s+//) {
                if($1 eq 'n') { $items[$typeid] = $2; $got|=1<<$typeid; ++$ngot; }
                elsif($1 eq 'c') { $calamity[$typeid] = $2; $corg|=1; }
                elsif($1 eq 'g') { $godsend[$typeid] = $2; $corg|=2; }
            }
            $context=" in item $typeid";
            if($corg) { push(@fragileitems, $typeid); }
        }
        elsif($line =~ s/^levels(\d):\s*(.*?)\s*$//) {
            my $typeid=int($1);
            $levels[$typeid]=[split(/,\s*/,$2)];
        }
        elsif($line =~ s/^unique:\s*//) {
            my %hash=();
	    while($line =~ s/([ubrtsde])="([^\"]*)"\s+// or
		  $line =~ s/([ubrtsde])=(\w+)\s+//) {
                if($1 eq 'u') { $hash{'userlevel'} = int($2); }
                elsif($1 eq 'b') { $hash{'baselevel'} = int($2); }
                elsif($1 eq 'r') { $hash{'levelrange'} = int($2); }
                elsif($1 eq 't') { $hash{'typeid'} = int($2); }
                elsif($1 eq 's') { $hash{'suffix'} = $2; }
                elsif($1 eq 'd') { $hash{'desc'} = $2; }
		elsif($1 eq 'e') { $hash{'enemies'} = $2; }
            }
            $context="";
	    $hash{'enemies'} //= ($hash{'desc'} =~ s/^([^!.])[!.]\s*(.*)$/$1/) ? $2 : '';
            if(!length($line)) { push(@uniques, \%hash); ++$gotu; $uniques{$hash{'suffix'}} = $#uniques; }
            else { debug("Error: trailing fields defining unique: '$line'",1); }
        }
        if(defined($context) and length($line)) {
            chomp($line);
            debug("Error: What's '$line'$context in $fn",0);
        }
    }
    while($got) {
        if(!($got&1)) { debug("Error: item#s not consecutive in $fn",1); }
        $got>>=1; 
    }
    debug("Got $ngot normal items and $gotu unique items.",0);
    close(IF);
}
