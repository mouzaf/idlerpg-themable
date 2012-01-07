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
    "writequestfile",
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
    "modsfile=s",
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
) or debug("Error: Could not parse command line. Try $0 --help\n",1);

$opts{help} and do { help(); exit 0; };

debug("Config: read $_: ".Dumper($opts{$_})) for keys(%opts);

my @items;
my @levels;
my @calamity;
my @godsend;
my @uniques;
my @fragileitems;
read_items();

my @quests;
my %events;
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
sub they($) { return $hesheit{$rps{$_[0]}{gender}}; }
sub them($) { return $himherit{$rps{$_[0]}{gender}}; }
sub their($) { return $hisherits{$rps{$_[0]}{gender}}; }

my $outbytes = 0; # sent bytes
my $primnick = $opts{botnick}; # for regain or register checks
my $inbytes = 0; # received bytes
my %onchan; # users on game channel
my %quest = restorequest();

my @junk = (); # [ time of junking, type, value+suffix, alignment ]

my $rpreport = 0; # constant for reporting top players
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
    $rps{$uname}{class} = substr($uclass,0,30);
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
    $rps{$uname}{nick} = "";
    $rps{$uname}{userhost} = "";
    $rps{$uname}{level} = 0;
    $rps{$uname}{online} = 0;
    $rps{$uname}{idled} = 0;
    $rps{$uname}{created} = time();
    $rps{$uname}{lastlogin} = time();
    $rps{$uname}{x} = int(rand($opts{mapx}));
    $rps{$uname}{y} = int(rand($opts{mapy}));
    $rps{$uname}{alignment}="n";
    $rps{$uname}{isadmin} = 1;
    $rps{$uname}{gender} = "u";
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
if ($opts{checkupdates}) {
    print "Checking for updates...\n\n";
    my $tempsock = IO::Socket::INET->new(PeerAddr=>"jotun.ultrazone.org:80",
                                         Timeout => 15);
    if ($tempsock) {
        print $tempsock "GET /g7/version.php?version=$version HTTP/1.1\r\n".
                        "Host: jotun.ultrazone.org:80\r\n\r\n";
        my($line,$newversion);
        while ($line=<$tempsock>) {
            chomp($line);
            next() unless $line;
            if ($line =~ /^Current version : (\S+)/) {
                if ($version ne $1) {
                    print "There is an update available! Changes include:\n";
                    $newversion=1;
                }
                else {
                    print "You are running the latest version (v$1).\n";
                    close($tempsock);
                    last();
                }
            }
            elsif ($newversion && $line =~ /^(  -? .+)/) { print "$1\n"; }
            elsif ($newversion && $line =~ /^URL: (.+)/) {
                print "\nGet the newest version from $1!\n";
                close($tempsock);
                last();
            }
        }
    }
    else { print debug("Could not connect to update server.")."\n"; }
}

print "\n".debug("Becoming a daemon...")."\n";
daemonize();

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
            while (index($buffer,"\n") != -1) {
                my $line = substr($buffer,0,index($buffer,"\n")+1);
                $buffer = substr($buffer,length($line));
                parse($line);
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
        if ($opts{'detectsplits'} && exists($split{substr($arg[0],1)})) {
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
        elsif ($opts{'detectsplits'} &&
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
            if (length("%auto_login") < 1024 && $opts{senduserlist}) {
                chanmsg(scalar(keys(%auto_login))." users matching ".
                        scalar(keys(%prev_online))." hosts automatically ".
                        "logged in; accounts: ".join(", ",keys(%auto_login)));
            }
            else {
                chanmsg(scalar(keys(%auto_login))." users matching ".
                        scalar(keys(%prev_online))." hosts automatically ".
                        "logged in.");
            }
            if ($opts{voiceonlogin}) {
                my @vnicks = map { $rps{$_}{nick} } keys(%auto_login);
                while (@vnicks) {
                    my @removed = splice(@vnicks,0,$opts{modesperline});
                    sts("MODE $opts{botchan} +".
                        ('v' x $opts{modesperline})." ".
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
            if ($arg[3] eq "\1version\1") {
                notice("\1VERSION IRPG bot v$version by jotun; ".
                       "http://idlerpg.net/\1",$usernick);
            }
            elsif ($arg[3] eq "peval") {
                if (!ha($username) || ($opts{ownerpevalonly} &&
                    $opts{owner} ne $username)) {
                    privmsg("You don't have access to PEVAL.", $usernick);
                }
                else {
                    my @peval = eval "@arg[4..$#arg]";
                    if (@peval >= 4 || length("@peval") > 1024) {
                        privmsg("Command produced too much output to send ".
                                "outright; queueing ".length("@peval").
                                " bytes in ".scalar(@peval)." items. Use ".
                                "CLEARQ to clear queue if needed.",$usernick,1);
                        privmsg($_,$usernick) for @peval;
                    }
                    else { privmsg($_,$usernick, 1) for @peval; }
                    privmsg("EVAL ERROR: $@", $usernick, 1) if $@;
                }
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
                        ++$registrations;
                        $lastreg = time();
                        $rps{$arg[4]}{next} = $opts{rpbase};
                        $rps{$arg[4]}{class} = "@arg[6..$#arg]";
                        $rps{$arg[4]}{level} = 0;
                        $rps{$arg[4]}{online} = 1;
                        $rps{$arg[4]}{nick} = $usernick;
                        $rps{$arg[4]}{userhost} = $arg[0];
                        $rps{$arg[4]}{created} = time();
                        $rps{$arg[4]}{lastlogin} = time();
                        $rps{$arg[4]}{pass} = crypt($arg[5],mksalt());
                        $rps{$arg[4]}{x} = int(rand($opts{mapx}));
                        $rps{$arg[4]}{y} = int(rand($opts{mapy}));
                        $rps{$arg[4]}{alignment}="n";
                        $rps{$arg[4]}{gender}="u";
                        $rps{$arg[4]}{isadmin} = 0;
                        for my $item (0..$#items) {
                            $rps{$arg[4]}{item}[$item] = 0;
                        }
                        for my $pen ("pen_mesg","pen_nick","pen_part",
                                     "pen_kick","pen_quit","pen_quest",
                                     "pen_logout","pen_logout") {
                            $rps{$arg[4]}{$pen} = 0;
                        }
                        chanmsg("Welcome $usernick\'s new player $arg[4], the ".
                                "@arg[6..$#arg]! Next level in ".
                                duration($opts{rpbase}).".");
                        privmsg("Success! Account $arg[4] created. You have ".
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
                if (!ha($username)) {
                    privmsg("You don't have access to DELOLD.", $usernick);
                }
                # insure it is a number
                elsif ($arg[4] !~ /^[\d\.]+$/) {
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
                if (!ha($username)) {
                    privmsg("You don't have access to DEL.", $usernick);
                }
                elsif (!defined($arg[4])) {
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
                if (!ha($username) || ($opts{owneraddonly} &&
                    $opts{owner} ne $username)) {
                    privmsg("You don't have access to MKADMIN.", $usernick);
                }
                elsif (!defined($arg[4])) {
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
                if (!ha($username) || ($opts{ownerdelonly} &&
                    $opts{owner} ne $username)) {
                    privmsg("You don't have access to DELADMIN.", $usernick);
                }
                elsif (!defined($arg[4])) {
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
            elsif ($arg[3] eq "hog") {
                if (!ha($username)) {
                    privmsg("You don't have access to HOG.", $usernick);
                }
                else {
                    chanmsg("$usernick has summoned the Hand of God.");
                    hog();
                }
            }
            elsif ($arg[3] eq "rehash") {
                if (!ha($username)) {
                    privmsg("You don't have access to REHASH.", $usernick);
                }
                else {
                    readconfig();
                    read_items();
                    read_events();
                    privmsg("Reread config file, items, and events.",$usernick,1);
                    $opts{botchan} =~ s/ .*//; # strip channel key if present
                }
            }
            elsif ($arg[3] eq "chpass") {
                if (!ha($username)) {
                    privmsg("You don't have access to CHPASS.", $usernick);
                }
                elsif (!defined($arg[5])) {
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
                if (!ha($username)) {
                    privmsg("You don't have access to CHUSER.", $usernick);
                }
                elsif (!defined($arg[5])) {
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
                if (!ha($username)) {
                    privmsg("You don't have access to CHCLASS.", $usernick);
                }
                elsif (!defined($arg[5])) {
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
                if (!ha($username)) {
                    privmsg("You don't have access to PUSH.", $usernick);
                }
                # insure it's a positive or negative, integral number of seconds
                elsif ($arg[5] !~ /^\-?\d+$/) {
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
                if (defined($username)) {
                    penalize($username,"logout");
                }
                else {
                    privmsg("You are not logged in.", $usernick);
                }
            }
            elsif ($arg[3] eq "newquest") {
                if (!ha($username)) {
                    privmsg("You don't have access to NEWQUEST.", $usernick);
                }
                elsif(@{$quest{questers}}) {
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
                    privmsg(join(", ",(@{$quest{questers}})[0..2]).", and ".
                            "$quest{questers}->[3] are on a quest to ".
                            "$quest{text}. Quest to complete in ".
                            duration($quest{qtime}-time()).".",$usernick);
                }
                elsif ($quest{type} == 2) {
                    privmsg(join(", ",(@{$quest{questers}})[0..2]).", and ".
                            "$quest{questers}->[3] are on a quest to ".
                            "$quest{text}. Participants must first reach ".
                            "[$quest{p1}->[0],$quest{p1}->[1]], then ".
                            "[$quest{p2}->[0],$quest{p2}->[1]].".
                            ($opts{mapurl}?" See $opts{mapurl} to monitor ".
                            "their journey's progress.":""),$usernick);
                }
            }
            elsif ($arg[3] eq "status" && $opts{statuscmd}) {
                if (!defined($username)) {
                    privmsg("You are not logged in.", $usernick);
                }
                # argument is optional
                elsif ($arg[4] && !exists($rps{$arg[4]})) {
                    privmsg("No such user.",$usernick);
                }
                elsif ($arg[4]) { # optional 'user' argument
                    privmsg("$arg[4]: Level $rps{$arg[4]}{level} ".
                            "$rps{$arg[4]}{class}; Status: O".
                            ($rps{$arg[4]}{online}?"n":"ff")."line; ".
                            "TTL: ".duration($rps{$arg[4]}{next})."; ".
                            "Idled: ".duration($rps{$arg[4]}{idled}).
                            "; Item sum: ".itemsum($arg[4]),$usernick);
                }
                else { # no argument, look up this user
                    privmsg("$username: Level $rps{$username}{level} ".
                            "$rps{$username}{class}; Status: O".
                            ($rps{$username}{online}?"n":"ff")."line; ".
                            "TTL: ".duration($rps{$username}{next})."; ".
                            "Idled: ".duration($rps{$username}{idled})."; ".
                            "Item sum: ".itemsum($username),$usernick);
                }
            }
            elsif ($arg[3] eq "whoami") {
                if (!defined($username)) {
                    privmsg("You are not logged in.", $usernick);
                }
                else {
                    privmsg("You are $username, the level ".
                            $rps{$username}{level}." $rps{$username}{class}. ".
                            "Next level in ".duration($rps{$username}{next}),
                            $usernick);
                }
            }
            elsif ($arg[3] eq "newpass") {
                if (!defined($username)) {
                    privmsg("You are not logged in.", $usernick)
                }
                elsif (!defined($arg[4])) {
                    privmsg("Try: NEWPASS <new password>", $usernick);
                }
                else {
                    $rps{$username}{pass} = crypt($arg[4],mksalt());
                    privmsg("Your password was changed.",$usernick);
                }
            }
            elsif ($arg[3] eq "align") {
                if (!defined($username)) {
                    privmsg("You are not logged in.", $usernick)
                }
                elsif (!defined($arg[4]) || (lc($arg[4]) ne "good" &&
                       lc($arg[4]) ne "neutral" && lc($arg[4]) ne "evil")) {
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
                if (!defined($username)) {
                    privmsg("You are not logged in.", $usernick)
                }
                elsif (!defined($arg[4]) || !defined($hesheit{lc($arg[4])})) {
                    privmsg("Try: GENDER <m|f|n>", $usernick);
                }
                else {
                    $rps{$username}{gender} = lc($arg[4]);
                    chanmsg("$username has changed gender to: ".lc($arg[4]).".");
                    privmsg("Your gender was changed to ".lc($arg[4]).".",
                            $usernick);
                }
            }
            elsif ($arg[3] eq "removeme") {
                if (!defined($username)) {
                    privmsg("You are not logged in.", $usernick)
                }
                else {
                    privmsg("Account $username removed.",$usernick);
                    chanmsg("$arg[0] removed his account, $username, the ".
                            $rps{$username}{class}.".");
                    delete($rps{$username});
                }
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
                if (!ha($username)) {
                    privmsg("You do not have access to DIE.", $usernick);
                }
                else {
                    $opts{reconnect} = 0;
                    writedb();
                    sts("QUIT :DIE from $arg[0]",1);
                }
            }
            elsif ($arg[3] eq "reloaddb") {
                if (!ha($username)) {
                    privmsg("You do not have access to RELOADDB.", $usernick);
                }
                elsif (!$pausemode) {
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
                if (!ha($username)) {
                    privmsg("You do not have access to BACKUP.", $usernick);
                }
                else {
                    backup();
                    privmsg("$opts{dbfile} copied to ".
                            ".dbbackup/$opts{dbfile}".time(),$usernick,1);
                }
            }
            elsif ($arg[3] eq "pause") {
                if (!ha($username)) {
                    privmsg("You do not have access to PAUSE.", $usernick);
                }
                else {
                    $pausemode = $pausemode ? 0 : 1;
                    privmsg("PAUSE_MODE set to $pausemode.",$usernick,1);
                }
            }
            elsif ($arg[3] eq "silent") {
                if (!ha($username)) {
                    privmsg("You do not have access to SILENT.", $usernick);
                }
                elsif (!defined($arg[4]) || $arg[4] < 0 || $arg[4] > 3) {
                    privmsg("Try: SILENT <mode>", $usernick,1);
                }
                else {
                    $silentmode = $arg[4];
                    privmsg("SILENT_MODE set to $silentmode.",$usernick,1);
                }
            }
            elsif ($arg[3] eq "jump") {
                if (!ha($username)) {
                    privmsg("You do not have access to JUMP.", $usernick);
                }
                elsif (!defined($arg[4])) {
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
                if (!ha($username)) {
                    privmsg("You do not have access to RESTART.", $usernick);
                }
                else {
                    writedb();
                    sts("QUIT :RESTART from $arg[0]",1);
                    close($sock);
                    exec("perl $0");
                }
            }
            elsif ($arg[3] eq "clearq") {
                if (!ha($username)) {
                    privmsg("You do not have access to CLEARQ.", $usernick);
                }
                else {
                    undef(@queue);
                    chanmsg("Outgoing message queue cleared by $arg[0].");
                    privmsg("Outgoing message queue cleared.",$usernick,1);
                }
            }
            elsif ($arg[3] eq "info") {
                my $info;
                if (!ha($username) && $opts{allowuserinfo}) {
                    $info = "IRPG bot v$version by jotun, ".
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
                if($arg[4]<0 or $arg[4]>$#items) {
                    notice("0 <= item <= $#items", $usernick);
                }
                elsif($arg[5] !~ m/^\d\d?\d?/) {
                    notice("0 <= level <= 999", $usernick); 
                }
                else { 
                    notice("itemlevel($arg[4],$arg[5]) = ".item_level($arg[4],$arg[5],'A')." $items[$arg[4]]", 
                           $usernick); 
                }
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

sub duration { # return human duration of seconds
    my $s = shift;
    return "NA ($s)" if $s !~ /^\d+$/;
    return sprintf("%d day%s, %02d:%02d:%02d",$s/86400,int($s/86400)==1?"":"s",
                   ($s%86400)/3600,($s%3600)/60,($s%60));
}

sub item_level {
    my ($typeid,$article) = ($_[0], ($_[2]?"$_[2] ":''));
    if(!defined($levels[$typeid])) { return "${article}level $_[1]"; }
    my ($lev,$ind)=(-1,-1);
    my ($marker,$op,$delta,$marklast);
    while($lev<$_[1]) {
        #print STDERR ("$lev<$_[1], ind=$ind".
        #              ($delta?", stepping=($marker,$op,$delta,$marklast)\n":"\n"));
        ++$lev;
        if($op) {
            $marker = ($op eq '+') ? $marker+$delta 
                : ($op eq '-') ? $marker-$delta 
                : $marker*$delta;
            # Ensure accuracy is sensibly represented at every step, 
            # as we need to check our bounds correctly, and don't
            # want errors to accumulate.
            my $point;
            if(($point = index($delta,'.'))>=0) {
                my $prec=length($delta)-$point-1;
                $marker=sprintf("%.${prec}f", $marker);
                #debug("$marker -> $fix {$delta, $point, $prec)");
            }
            if(defined($marklast) && 
               (($op eq '-') ? $marker<=$marklast : $marker>=$marklast)) {
                undef($op); 
            }
        }
        else {
            ++$ind;
            if($levels[$typeid][$ind] =~ /%{([\d.]+)\#([-+*])([\d.]+)(?:\#([\d.]+))?}%/) {
                ($marker,$op,$delta,$marklast) = ($1,$2,$3,$4);
            }
        }
    }
    my $template = $levels[$typeid][$ind];
    if($template !~ s/^!a // and $article) { $template = $article . $template; }
    if(defined($marker)) {
        $template =~ s/%{([\d.]+)\#([-+*])([\d.]+)(?:\#([\d.]+))?}%/$marker/;
    }
    return $template;
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
    my $event = get_event($win?'W':'L', $player, $rand);
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
    if (rand((12*86400)/$opts{self_clock}) < $onlinegood) { goodness(); }

    moveplayers();
    managejunk();

    # statements using $rpreport do not bother with scaling by the clock because
    # $rpreport is adjusted by the number of seconds since last rpcheck()
    if ($rpreport%120==0 && $opts{writequestfile}) { writequestfile(); }
    if (defined($quest{qtime}) and time() > $quest{qtime}) {
        if (!@{$quest{questers}}) { quest(); }
        elsif ($quest{type} == 1) {
            chanmsg_l(join(", ",(@{$quest{questers}})[0..2]).", and ".
                      "$quest{questers}->[3] have blessed the realm by ".
                      "completing their quest! 25% of their burden is ".
                      "eliminated.");
            for (@{$quest{questers}}) {
                $rps{$_}{next} = int($rps{$_}{next} * .75);
            }
            undef(@{$quest{questers}});
            $quest{qtime} = time() + 21600;
        }
        # quest type 2 awards are handled in moveplayers()
    }
    if ($rpreport && $rpreport%36000==0) { # 10 hours
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
    if ($rpreport%3600==0 && $rpreport) { # 1 hour
        my @players = grep { $rps{$_}{online} &&
                             $rps{$_}{level} > 44 } keys(%rps);
        # 20% of all players must be level 45+
        if ((scalar(@players)/scalar(grep { $rps{$_}{online} } keys(%rps))) > .15) {
            challenge_opp($players[int(rand(@players))]);
        }
        while (@bans) {
            sts("MODE $opts{botchan} -bbbb :@bans[0..3]");
            splice(@bans,0,4);
        }
    }
    if ($rpreport%1800==0) { # 30 mins
        if ($opts{botnick} ne $primnick) {
            (my $ghostcmd = $opts{botghostcmd}) =~ s/%(owner|botnick)%/$opts{$1}/eg;
            sts($ghostcmd) if $ghostcmd;
            sts("NICK $primnick");
        }
    }
    if ($rpreport%600==0 && $pausemode) { # warn every 10m
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
                    if ($rps{$k}{level} > 60) {
                        $rps{$k}{next} = int(($opts{rpbase} *
                                             ($opts{rpstep}**60)) +
                                             (86400*($rps{$k}{level} - 60)));
                    }
                    else {
                        $rps{$k}{next} = int($opts{rpbase} *
                                             ($opts{rpstep}**$rps{$k}{level}));
                    }
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
        if (!$pausemode && $rpreport%60==0) { writedb(); }
        $rpreport += $opts{self_clock};
        $lasttime = $curtime;
    }
}

sub challenge_opp { # pit argument player against random player
    my $u = shift;
    if ($rps{$u}{level} < 25) { return unless rand(4) < 1; }
    my @opps = grep { $rps{$_}{online} && $u ne $_ } keys(%rps);
    return unless @opps;
    my $opp = $opps[int(rand(@opps))];
    $opp = $primnick if rand(@opps+1) < 1;
    my $mysum = itemsum($u,1);
    my $oppsum = itemsum($opp,1);
    my $myroll = int(rand($mysum));
    my $opproll = int(rand($oppsum));
    if ($myroll >= $opproll) {
        my $gain = ($opp eq $primnick)?20:int($rps{$opp}{level}/4);
        $gain = 7 if $gain < 7;
        $gain = int(($gain/100)*$rps{$u}{next});
        chanmsg_l("$u [$myroll/$mysum] has challenged $opp [$opproll/".
                  "$oppsum] in combat and won! ".duration($gain)." is ".
                  "removed from $u\'s clock.");
        $rps{$u}{next} -= $gain;
        chanmsg("$u reaches next level in ".duration($rps{$u}{next}).".");
        my $csfactor = $rps{$u}{alignment} eq "g" ? 50 :
                       $rps{$u}{alignment} eq "e" ? 20 :
                       35;
        if (rand($csfactor) < 1 && $opp ne $primnick) {
            $gain = int(((5 + int(rand(20)))/100) * $rps{$opp}{next});
            chanmsg_l("$u has dealt $opp a Critical Strike! ".
                      duration($gain)." is added to $opp\'s clock.");
            $rps{$opp}{next} += $gain;
            chanmsg("$opp reaches next level in ".duration($rps{$opp}{next}).
                    ".");
        }
        elsif (rand(25) < 1 && $opp ne $primnick && $rps{$u}{level} > 19) {
            my $typeid = int(rand(@items));
            my $type = $items[$typeid];
            if (int($rps{$opp}{item}[$typeid]) > int($rps{$u}{item}[$typeid])) {
                chanmsg_l("In the fierce battle, $opp dropped ".their($opp)." ".
                          item_level($typeid,int($rps{$opp}{item}[$typeid])).
                          " $type! $u picks it up, tossing ".their($u)." old ".
                          item_level($typeid,int($rps{$u}{item}[$typeid])).
                          " $type to $opp.");
                my $tempitem = $rps{$u}{item}[$typeid];
                $rps{$u}{item}[$typeid]=$rps{$opp}{item}[$typeid];
                $rps{$opp}{item}[$typeid] = $tempitem;
            }
        }
    }
    else {
        my $gain = ($opp eq $primnick)?10:int($rps{$opp}{level}/7);
        $gain = 7 if $gain < 7;
        $gain = int(($gain/100)*$rps{$u}{next});
        chanmsg_l("$u [$myroll/$mysum] has challenged $opp [$opproll/".
                  "$oppsum] in combat and lost! ".duration($gain)." is ".
                  "added to $u\'s clock.");
        $rps{$u}{next} += $gain;
        chanmsg("$u reaches next level in ".duration($rps{$u}{next}).".");
    }
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

sub unique_notice($$$) {
    my $string=$_[0];
    $string =~ s/%ulevel%/$_[1]/g;
    $string =~ s/%nick%/$_[2]/g;
    return "The light of the gods shines down upon you! You have found the level $_[1] $string";
}

sub find_item { # find item for argument player
    my $u = shift;
    my $level = 1;
    my $ulevel;
    for my $num (1 .. int($rps{$u}{level}*1.5)) {
        if (rand(1.4**($num/4)) < 1) {
            $level = $num;
        }
    }
    for my $m (0 .. $#uniques) {
        my $uniq = $uniques[$m];
        if ($rps{$u}{level} >= $uniq->{userlevel} && rand(40) < 1) {
            $ulevel = $uniq->{baselevel} + int(rand($uniq->{levelrange}));
            my $utypeid = $uniq->{typeid};
            if ($ulevel >= $level && $ulevel > int($rps{$u}{item}[$utypeid])) {
                my $notice=unique_notice($uniq->{desc}, $ulevel, $rps{$u}{nick});
                notice($notice,$rps{$u}{nick});
                clog($notice);
                $rps{$u}{item}[$utypeid] = "$ulevel$uniq->{suffix}";
                return;
            }
        }
    }

    my $typeid = int(rand(@items));
    my $type = $items[$typeid];
    if ($level > int($rps{$u}{item}[$typeid])) {
        my $notice = "You found ".item_level($typeid,$level,'a').
                     " $type! Your current $type is only ".
                     item_level($typeid,int($rps{$u}{item}[$typeid])).
                     ", so it seems Luck is with you!";
        notice($notice,$rps{$u}{nick});
        clog($notice);
        $rps{$u}{item}[$typeid] = $level;
    }
    else {
        notice("You found ".item_level($typeid,$level,'a').
               " $type. Your current $type is ".
               item_level($typeid,int($rps{$u}{item}[$typeid])).
               ", so it seems Luck is against you. ".
               "You toss the $type.",$rps{$u}{nick});
    }
}

sub loaddb { # load the players database
    backup();
    my $l;
    %rps = ();
    if (!open(RPS,$opts{dbfile}) && -e $opts{dbfile}) {
        sts("QUIT :loaddb() failed: $!");
    }
    while ($l=<RPS>) {
        chomp($l);
        next if $l =~ /^#/; # skip comments
        my @i = split("\t",$l);
        print Dumper(@i) if(@i < 32 or @i > 33);
        if (@i < 32 or @i > 33) {
            sts("QUIT: Anomaly in loaddb(); line $. of $opts{dbfile} has ".
                "wrong fields (".scalar(@i).")");
            debug("Anomaly in loaddb(); line $. of $opts{dbfile} has wrong ".
                "fields (".scalar(@i).")",1);
        }
        if (!$sock) { # if not RELOADDB
            if ($i[8]) { $prev_online{$i[7]}=$i[0]; } # log back in
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
        $rps{$i[0]}{item}[0],
        $rps{$i[0]}{item}[1],
        $rps{$i[0]}{item}[2],
        $rps{$i[0]}{item}[3],
        $rps{$i[0]}{item}[4],
        $rps{$i[0]}{item}[5],
        $rps{$i[0]}{item}[6],
        $rps{$i[0]}{item}[7],
        $rps{$i[0]}{item}[8],
        $rps{$i[0]}{item}[9],
        $rps{$i[0]}{alignment},
        $rps{$i[0]}{gender}) = (@i[1..7],($sock?$i[8]:0),@i[9..31],($i[32]||"u"));
    }
    close(RPS);
    debug("loaddb(): loaded ".scalar(keys(%rps))." accounts, ".
          scalar(keys(%prev_online))." previously online.");
}

sub moveplayers {
    return unless $lasttime > 1;
    my $onlinecount = grep { $rps{$_}{online} } keys %rps;
    return unless $onlinecount;
    for (my $i=0;$i<$opts{self_clock};++$i) {
        # temporary hash to hold player positions, detect collisions
        my %positions = ();
        if ($quest{type} == 2 && @{$quest{questers}}) {
            my $allgo = 1; # have all users reached <p1|p2>?
            my ($x,$y) = @{$quest{"p$quest{stage}"}};
            for (@{$quest{questers}}) {
                if ($rps{$_}{x} != $x || $rps{$_}{y} != $y) { $allgo=0; last; }
            }
            # all participants have reached point 1, now point 2
            if ($quest{stage}==1 && $allgo) {
                $quest{stage}=2;
                writequestfile();
            }
            elsif ($quest{stage} == 2 && $allgo) {
                chanmsg_l(join(", ",(@{$quest{questers}})[0..2]).", ".
                          "and $quest{questers}->[3] have completed their ".
                          "journey! 25% of their burden is eliminated.");
                for (@{$quest{questers}}) {
                    $rps{$_}{next} = int($rps{$_}{next} * .75);
                }
                undef(@{$quest{questers}});
                $quest{qtime} = time() + 21600; # next quest starts in 6 hours
                $quest{type} = 1; # probably not needed
                writequestfile();
            }
            else {
                for (@{$quest{questers}}) {
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
            if (1) {
                my(%temp,$player);
                # load keys of %temp with online users
                ++@temp{grep { $rps{$_}{online} } keys(%rps)};
                # delete questers from list
                delete(@temp{@{$quest{questers}}});
                while ($player = each(%temp)) {
                    $rps{$player}{x} += int(rand(3))-1;
                    $rps{$player}{y} += int(rand(3))-1;
                    # if player goes over edge, wrap them back around
                    if ($rps{$player}{x} > $opts{mapx}) { $rps{$player}{x}=0; }
                    if ($rps{$player}{y} > $opts{mapy}) { $rps{$player}{y}=0; }
                    if ($rps{$player}{x} < 0) { $rps{$player}{x}=$opts{mapx}; }
                    if ($rps{$player}{y} < 0) { $rps{$player}{y}=$opts{mapy}; }

                    if (exists($positions{$rps{$player}{x}}{$rps{$player}{y}}) &&
                        !$positions{$rps{$player}{x}}{$rps{$player}{y}}{battled}) {
                        if ($rps{$positions{$rps{$player}{x}}{$rps{$player}{y}}{user}}{isadmin} &&
                            !$rps{$player}{isadmin} && rand(100) < 1) {
                            chanmsg("$player encounters ".
                               $positions{$rps{$player}{x}}{$rps{$player}{y}}{user}.
                                    " and bows humbly.");
                        }
                        if (rand($onlinecount) < 1) {
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
        }
        else {
            for my $player (keys(%rps)) {
                next unless $rps{$player}{online};
                $rps{$player}{x} += int(rand(3))-1;
                $rps{$player}{y} += int(rand(3))-1;
                # if player goes over edge, wrap them back around
                if ($rps{$player}{x} > $opts{mapx}) { $rps{$player}{x} = 0; }
                if ($rps{$player}{y} > $opts{mapy}) { $rps{$player}{y} = 0; }
                if ($rps{$player}{x} < 0) { $rps{$player}{x} = $opts{mapx}; }
                if ($rps{$player}{y} < 0) { $rps{$player}{y} = $opts{mapy}; }
                if (exists($positions{$rps{$player}{x}}{$rps{$player}{y}}) &&
                    !$positions{$rps{$player}{x}}{$rps{$player}{y}}{battled}) {
                    if ($rps{$positions{$rps{$player}{x}}{$rps{$player}{y}}{user}}{isadmin} &&
                        !$rps{$player}{isadmin} && rand(100) < 1) {
                        chanmsg("$player encounters ".
                           $positions{$rps{$player}{x}}{$rps{$player}{y}}{user}.
                                " and bows humbly.");
                    }
                    if (rand($onlinecount) < 1) {
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
    }
}

sub managejunk {
    if(@junk > 10) { shift(@junk); }
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
  --rppenstep          PENALTY_SECS=(PENALTY*(RPPENSTEP**CURRENT_LEVEL))

";
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
            $sum = itemsum($u) if $sum < itemsum($u);
        }
        return $sum+1;
    }
    if (!exists($rps{$user})) { return -1; }
    $sum += int($rps{$user}{item}[$_]) for (0..$#items);
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

sub rewrite_event($$$) {
    my ($s,$p,$r)=@_;
    $s =~ s/%player%/$p/g;
    $s =~ s/%(he|she|they)%/they($p)/eg;
    $s =~ s/%(his|her|their)%/their($p)/eg;
    $s =~ s/%(him|her|them)%/them($p)/eg;
    while($s =~ m/%{(.*?)}%/) {
        my ($start, $end)=($-[0], $+[0]);
        my $len=$end-$start;
        if(index($1,'|')>=0 or index($1,'#')<0) {
            my @list=split(/\|/, $1);
            substr($s,$start,$len) = $list[int(rand(@list))];
        } elsif($1 =~ m/^([\d.]+)\#(?:([-+])([\d.]+))?\#([\d.]+)$/) {
            my $step = $3 ? $3 * ($2 eq '-'?-1:1) : 1;
            my $numsteps = int(($4-$1)/$step)+1;
            substr($s,$start,$len) = $1+int($r*$numsteps)*$step;
        } else {
            debug("No choice in macro ". substr($s,$start,$end));
            substr($s,$start,$len) = substr($s,$start+2,$end-2);
        }
    }
    return $s;
}

sub modify_item($) {
    my @change = ('loses', 'gains');
    my @timechange = ('terrible calamity has slowed',
                      'wondrous godsend has accelerated');
    my $good = ($_[0] > 0);
    my @players = grep { $rps{$_}{online} } keys(%rps);
    return unless @players;
    my $player = $players[rand(@players)];
    if (rand(10) < 1) {
        my($typeid,$change);
        while(!$change) {
            $typeid = $fragileitems[rand(@fragileitems)];
            $change = ($good ? $godsend[$typeid] : $calamity[$typeid]);
        }
        $change = rewrite_event($change, $player, undef); # random number not used currently
        my $type = $items[$typeid];
        $change = "${player}$change" .
            " $player\'s $type $change[$good] 10% of its effectiveness.";
        chanmsg_l($change);

        my $suffix="";
        if ($rps{$player}{item}[$typeid] =~ /(\D)$/) { $suffix=$1; }
        $rps{$player}{item}[$typeid] = int(int($rps{$player}{item}[$typeid]) * (1+$_[0]*.1));
        $rps{$player}{item}[$typeid].=$suffix;
    }
    else {
        my $rand = rand();
        my $time = int(int(5 + $rand*8) / 100 * $rps{$player}{next});
        my $actioned = get_event($good?'G':'C', $player, $rand);
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
    if ($quest{type} == 1) {
        $quest{qtime} = time()+43200+int(rand(43201));
        chanmsg(join(", ",(@{$quest{questers}})[0..2]).", and ".
                "$quest{questers}->[3] have been chosen by the gods to ".
                "$quest{text}. Quest to end in ".duration($quest{qtime}-time()).
                ".");
    }
    elsif ($quest{type} == 2) {
        chanmsg(join(", ",(@{$quest{questers}})[0..2]).", and ".
                "$quest{questers}->[3] have been chosen by the gods to ".
                "$quest{text}. Participants must first reach [$quest{p1}->[0],".
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
            chanmsg_l("$k\'s prudence and self-regard has brought the ".
                      "wrath of the gods upon the realm. All your great ".
                      "wickedness makes you as it were heavy with lead, ".
                      "and to tend downwards with great weight and ".
                      "pressure towards hell. Therefore have you drawn ".
                      "yourselves 15 steps closer to that gaping maw.");
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

sub clog {
    my $mesg = shift;
    open(B,">>$opts{modsfile}") or do {
        debug("Error: Cannot open $opts{modsfile}: $!");
        chanmsg("Error: Cannot open $opts{modsfile}: $!");
        return $mesg;
    };
    print B ts()."$mesg\n";
    close(B);
    return $mesg;
}

sub backup() {
    if (! -d ".dbbackup/") { mkdir(".dbbackup",0700); }
    if ($^O ne "MSWin32") {
        system("cp $opts{dbfile} .dbbackup/$opts{dbfile}".time());
    }
    else {
        system("copy $opts{dbfile} .dbbackup\\$opts{dbfile}".time());
    }
}

sub penalize {
    my %why = (#quit=>'', part=>'', # don't talk to them after they leave
               privmsg=>'privmsg', notice=>'notice',
               nick=>"nick change", kick=>'being kicked', 'logout'=>'logging out');

    my $username = shift;
    return 0 if !defined($username);
    return 0 if !exists($rps{$username});
    my $type = shift;
    my $pen = 0;
    my $why = $why{$type};
    my $pentype;
    questpencheck($username);
    if ($type eq "quit") {
        $pen = int(20 * ($opts{rppenstep}**$rps{$username}{level}));
        $pentype = 'pen_quit';
        $rps{$username}{online}=0;
    }
    elsif ($type eq "nick") {
        my $newnick = shift;
        $pen = int(30 * ($opts{rppenstep}**$rps{$username}{level}));
        $pentype = 'pen_nick';
        $rps{$username}{nick} = substr($newnick,1);
        substr($rps{$username}{userhost},0,length($rps{$username}{nick})) =
            substr($newnick,1);
    }
    elsif ($type eq "privmsg" || $type eq "notice") {
        $pen = int(shift(@_) * ($opts{rppenstep}**$rps{$username}{level}));
        $pentype = 'pen_mesg';
    }
    elsif ($type eq "part") {
        $pen = int(200 * ($opts{rppenstep}**$rps{$username}{level}));
        $pentype = 'pen_part';
        $rps{$username}{online}=0;
    }
    elsif ($type eq "kick") {
        $pen = int(250 * ($opts{rppenstep}**$rps{$username}{level}));
        $pentype = 'pen_kick';
        $rps{$username}{online}=0;
    }
    elsif ($type eq "logout") {
        $pen = int(20 * ($opts{rppenstep}**$rps{$username}{level}));
        $pentype = 'pen_logout';
        $rps{$username}{online}=0;
    }
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

sub debug {
    (my $text = shift) =~ s/[\r\n]//g;
    my $die = shift;
    if ($opts{debug} || $opts{verbose}) {
        open(DBG,">>$opts{debugfile}") or do {
            chanmsg("Error: Cannot open debug file: $!");
            return;
        };
        print DBG ts()."$text\n";
        close(DBG);
    }
    if ($die) { die("$text\n"); }
    return $text;
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
        debug("Error: Attempted ha() for invalid username \"$user\"");
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

sub collision_fight {
    my($u,$opp) = @_;
    my $mysum = itemsum($u,1);
    my $oppsum = itemsum($opp,1);
    my $myroll = int(rand($mysum));
    my $opproll = int(rand($oppsum));
    if ($myroll >= $opproll) {
        my $gain = int($rps{$opp}{level}/4);
        $gain = 7 if $gain < 7;
        $gain = int(($gain/100)*$rps{$u}{next});
        chanmsg_l("$u [$myroll/$mysum] has come upon $opp [$opproll/$oppsum] ".
                  "and taken ".them($opp)." in combat! ".duration($gain).
                  " is removed from $u\'s clock.");
        $rps{$u}{next} -= $gain;
        chanmsg("$u reaches next level in ".duration($rps{$u}{next}).".");
        if (rand(35) < 1 && $opp ne $primnick) {
            $gain = int(((5 + int(rand(20)))/100) * $rps{$opp}{next});
            chanmsg_l("$u has dealt $opp a Critical Strike! ".
                      duration($gain)." is added to $opp\'s clock.");
            $rps{$opp}{next} += $gain;
            chanmsg("$opp reaches next level in ".duration($rps{$opp}{next}).
                    ".");
        }
        elsif (rand(25) < 1 && $opp ne $primnick && $rps{$u}{level} > 19) {
            my $typeid = int(rand(@items));
            my $type = $items[$typeid];
            if (int($rps{$opp}{item}[$typeid]) > int($rps{$u}{item}[$typeid])) {
                chanmsg_l("In the fierce battle, $opp dropped ".their($opp)." level ".
                          int($rps{$opp}{item}[$typeid])." $type! $u picks it up, ".
                          "tossing ".their($opp)." old level ".int($rps{$u}{item}[$typeid]).
                          " $type to $opp.");
                my $tempitem = $rps{$u}{item}[$typeid];
                $rps{$u}{item}[$typeid]=$rps{$opp}{item}[$typeid];
                $rps{$opp}{item}[$typeid] = $tempitem;
            }
        }
    }
    else {
        my $gain = ($opp eq $primnick)?10:int($rps{$opp}{level}/7);
        $gain = 7 if $gain < 7;
        $gain = int(($gain/100)*$rps{$u}{next});
        chanmsg_l("$u [$myroll/$mysum] has come upon $opp [$opproll/$oppsum".
                  "] and been defeated in combat! ".duration($gain)." is ".
                  "added to $u\'s clock.");
        $rps{$u}{next} += $gain;
        chanmsg("$u reaches next level in ".duration($rps{$u}{next}).".");
    }
}

sub restorequest {
    my %questdef = (
                    questers => [],
                    p1 => [], # point 1 for q2
                    p2 => [], # point 2 for q2
                    qtime => time() + int(rand(21600)), # first quest starts in <=6 hours
                    text => "",
                    type => 1,
                    stage => 1); # quest info
    return %questdef unless ($opts{writequestfile} and open(QF, "<$opts{writequestfile}"));
    my $type;
    while(<QF>) {
        if(m/^T (.*?)\s*$/) { $questdef{text} = $1; }
        elsif(m/^Y ([12])\s*$/) { $type = $questdef{type} = int($1); }
        elsif(m/^S (\d+)\s*$/) { $questdef{$type==1?'qtime':'stage'} = int($1); }
        elsif($type==2 and m/^P (\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s*$/) 
        { $questdef{p1}=[$1,$2]; $questdef{p2}=[$3,$4]; }
        elsif(m/^P(\d) (\S+)/) { $questdef{questers}->[$1] = $2; }
        else { debug("Unknown line in questfile $opts{writequestfile}: $_"); }
    }
    close(QF);
    return %questdef;
}

sub writequestfile {
    return unless $opts{writequestfile};
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

sub goodness {
    my @players = grep { $rps{$_}{alignment} eq "g" &&
                         $rps{$_}{online} } keys(%rps);
    return unless @players > 1;
    splice(@players,int(rand(@players)),1) while @players > 2;
    my $gain = 5 + int(rand(8));
    chanmsg_l("$players[0] and $players[1] have not let the iniquities of ".
              "evil men poison them. Together have they prayed to their ".
              "god, and it is his light that now shines upon them. $gain\% ".
              "of their time is removed from their clocks.");
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
        my $typeid = int(rand(@items));
        my $type = $items[$typeid];
        if (int($rps{$target}{item}[$typeid]) > int($rps{$me}{item}[$typeid])) {
            my $tempitem = $rps{$me}{item}[$typeid];
            $rps{$me}{item}[$typeid] = $rps{$target}{item}[$typeid];
            $rps{$target}{item}[$typeid] = $tempitem;
            chanmsg_l("$me stole $target\'s level ".
                      int($rps{$me}{item}[$typeid])." $type while ".they($target).
                      "were sleeping! $me leaves ".their($me)." old level ".
                      int($rps{$target}{item}[$typeid])." $type behind, ".
                      "which $target then takes.");
        }
        else {
            notice("You made to steal $target\'s $type, but realized it was ".
                   "lower level than your own. You creep back into the ".
                   "shadows.",$rps{$me}{nick});
        }
    }
    else { # being evil only pays about half of the time...
        my $gain = 1 + int(rand(5));
        chanmsg_l("$me is forsaken by ".their($me)." evil god. ".
                  duration(int($rps{$me}{next} * ($gain/100)))." is added ".
                  "to ".their($me)." clock.");
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
                        "item0",
                        "item1",
                        "item2",
                        "item3",
                        "item4",
                        "item5",
                        "item6",
                        "item7",
                        "item8",
                        "item9",
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
                                $rps{$k}{item}[0],
                                $rps{$k}{item}[1],
                                $rps{$k}{item}[2],
                                $rps{$k}{item}[3],
                                $rps{$k}{item}[4],
                                $rps{$k}{item}[5],
                                $rps{$k}{item}[6],
                                $rps{$k}{item}[7],
                                $rps{$k}{item}[8],
                                $rps{$k}{item}[9],
                                $rps{$k}{alignment},
                                $rps{$k}{gender}||"u")."\n";
        }
    }
    close(RPS);
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
        my($line,$key,$val);
        while ($line=<CONF>) {
            next() if $line =~ /^#/; # skip comments
            $line =~ s/[\r\n]//g;
            $line =~ s/^\s+//g;
            next() if !length($line); # skip blank lines
            ($key,$val) = split(/\s+/,$line,2);
            $key = lc($key);
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
    }
}

sub read_events {
    if (!open(Q,$opts{eventsfile})) {
        return chanmsg("ERROR: Failed to open $opts{eventsfile}: $!");
    }
    @quests = ();
    %events = (G => [], C => [], W => [], L => []);
    while (my $line = <Q>) {
        if ($line =~ /^([GCWL])\s+(.*)/) { push(@{$events{$1}}, $2); }
        elsif ($line =~ /^Q1 (.*)/) {
            push(@quests, { type=>1, text=>$1 });
        }
        elsif ($line =~ /^Q2 (\d+) (\d+) (\d+) (\d+) (.*)/) {
            push(@quests,
                 { type=>2, text=>$5, stage=>1, p1=>[$1,$2], p2=>[$3,$4] });
        }
        else { debug("Event in $opts{eventsfile} unknown: $line",0); }
    }
    close(Q);
    debug("Read ".@{$events{G}}." godsends, ".@{$events{C}}." calamaties, ".
          @{$events{W}}." HOG wins, ".@{$events{L}}." HOG losses, and ".
          @quests." quests.",0);
    # Must be at least one HOG win and lose line
    if(!@{$events{W}}) { push(@{$events{W}},"Weird stuff happened, pushing %player%"); }
    if(!@{$events{L}}) { push(@{$events{L}},"Weird stuff happened, pulling %player%"); }
}

sub get_event($$$) {
    return rewrite_event($events{$_[0]}[int(rand(@{$events{$_[0]}}))], $_[1], $_[2]);
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
    my ($got, $gotu)=(0,0);
    my ($line,$ix,$key,$val);
    while($line=<IF>) {
        next if $line =~ /^#/; # skip comments
        $line =~ s/^\s+//g;
        my $context;
        if($line =~ s/^item(\d):\s*//) {
            my $typeid=int($1);
            if($got>>$typeid & 1 and $line =~ m/n=/) {
                debug("Already have item$typeid = $items[$typeid]",0);
            }
            my $corg=0;
            while($line =~ s/([ncg])="([^\"]*)"\s+// or
                  $line =~ s/([ncg])=(\w+)\s+//) {
                if($1 eq 'n') { $items[$typeid] = $2; $got|=1<<$typeid; }
                elsif($1 eq 'c') { $calamity[$typeid] = $2; $corg=1; }
                elsif($1 eq 'g') { $godsend[$typeid] = $2; $corg=1; }
            }
            $context="in item $typeid";
            if($corg) { push(@fragileitems, $typeid); }
        }
        elsif($line =~ s/^levels(\d):\s*(.*?)\s*$//) {
            my $typeid=int($1);
            $levels[$typeid]=[split(/,\s*/,$2)];
        }
        elsif($line =~ s/^unique:\s*//) {
            my %hash=();
            while($line =~ s/([ubrtsd])="([^\"]*)"\s+// or
                  $line =~ s/([ubrtsd])=(\w+)\s+//) {
                if($1 eq 'u') { $hash{'userlevel'} = int($2); }
                elsif($1 eq 'b') { $hash{'baselevel'} = int($2); }
                elsif($1 eq 'r') { $hash{'levelrange'} = int($2); }
                elsif($1 eq 't') { $hash{'typeid'} = int($2); }
                elsif($1 eq 's') { $hash{'suffix'} = $2; }
                elsif($1 eq 'd') { $hash{'desc'} = $2; }
            }
            $context="";
            if(!length($line)) { push(@uniques, \%hash); ++$gotu; }
        }
        if(defined($context) and length($line)) {
            chomp($line);
            debug("Error: What's '$line'$context in $fn",0);
        }
    }
    if($got != 0x3ff) {
        debug("Error: Didn't find 10 items in $fn",1);
    }
    debug("Got all 10 normal items and $gotu unique items.",0);
    close(IF);
}
