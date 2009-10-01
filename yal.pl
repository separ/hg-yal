#!/usr/bin/perl

###############
#
# Realtime log time analyser for NWN adapted quite heavily for the Higher Ground mod
#
# (C) Claus Ekstrom 2008
#
# Released under GPLv3, see http://www.gnu.org/licenses/gpl-3.0.html
#
# Some layout based quite heavily on the NWN log analyser by bort http://highergroundpoa.proboards3.com/index.cgi?board=Tavern&action=display&thread=1196935422
#
# This work is far from finished. Actually it's hardly begun. Enjoy, modify and feel free to suggest things you'd like to see included if you're not a perl hacker yourself.
#
# Newest version of the perl script can be found at 4http://www.ekstroem.com/nwn/nwn.pl
################



#
# ToDo: 
#
# Size of scroll bit of windows
# Total damage/type
# Hit vs non-concealed targets
# shackled players --- fixed
# DC spell success ---fixed

use Tk;
use Tk::LabEntry;
use Tk::BrowseEntry;
use Tk::HList;
use Tk::ItemStyle;
# use Tk::Balloon;
use Date::Format;
use Date::Parse;

use XML::Simple; # TODO: remove and use regexp to parse hgdata.xml
use File::Copy; # for copying the runfile on run-end

use subs qw/beep/;
use warnings;
use strict;

my $version = "0.1.4b";
my $kills = 0;
my $deaths = 0;
my $totalxp = 0;
my $toon = "";
my $hits = 0;
my %paracount = ();    # Number of paragon hell monsters
my $totalmobkills = 0; # Number of non-party member kills 
my $statusmessage ="";
my $lastkiller = "";
my $lastkilled = "";
my $logfilenumber = 1;
my $currentlogfile = "nwclientLog1.txt";
my $cfgfile = "yal.cfg";
my %timers = ();   # A hash of arrays
my %Effecttimers = ();
my @grtimer = ();
my @gstimer = ();
my $timertext = "";
my $other = "";
my $hitfrequency = 0;
my $defencefrequency = 0;
my $hitfrequencyweight = 30;
my %damage = ();

my $shamelessadvertising = 0;

my $gearcontainer = "";
my $next_item_rarity = '';
my $bankchest = "default";
my $lastentry = "";
my $saverunbuffer;
my $savefiletimer;
# ills hacking my $othertimers;
my $effectid;     # Id to keep information about who effect listings concern

my $debug = 0;
my $parsetime = 3000;  # The number of miliseconds between each parsing of the file

# for edits by Separ
my $server = "";
my $srv_time = 0;
my $myserverwho = 0;
my $catchpartywho = 0;
my $server_uptime = 0;
my $server_round = 0; # every 6 seconds a new round.
my $uptime_secs = 0;
my $uptimeat = 0; # at which time did we catch the uptime msg
my $logfile_info = "?";
my $current_area = '';
my $current_map = '';
my $last_run = ''; # which non-ignore area == run were we last in?
my %hg_maps = ();
my %hg_areas = ();
my $parse_sub_mode = '';
my $current_save_file = ''; # name of file we're saving the current run to
my $log_start_ts = 0; # first timestamp we've seen in the log

#
# this is to hold the chat_dialog
#
my $chatlog_dialog;
my $chatlog;

#
# The following hashes keeps most of the information
#
my %kills = ();       # Hash of # kills
my %deaths = ();      # Hash of # deaths
my %party = ();       # Hash of party members
my %swings = ();
my %swingsagainst = ();
my %hits = ();
my %crits = ();
my %dodge = ();
my %damage_done = ();
my %damage_taken = ();
my %damage_takenstr = ();
my %elemental_immunities = ();
my %partykiller = ();
my %partykilled = ();
my %partyhits = ();
my %partyattacks = ();
my %badtooncounter = ();   # Counts the number of attacks on Mammon's tears, infernal machines etc. Purely for pointing the finger at someone
my %listofplayers = ();
my %hitpercentage = ();


my %Gear = ();
my %AB = ();
my %MinAC = ();
my %MaxAC = ();
my %immune = ();
my %conceal = ();
my %SR = ();
my %TR = ();
my %dam_taken_detail = ();

#
# The following hashes are more detailed and contain information split on attacker and defender. everything should eventually go into those as the program evolves
#
my %Saves = ();
my %TotalDamage = ();
my %Kills = (); 
my %Hits = ();
my %Swings = ();
my %Crits = ();
my %Conceals = ();
my %AbilityChecks = ();
my %SkillChecks = ();
my %DamageTypesDealt = ();
my %Disarm = ();
my %Effects = ();
#ills effects
my %Effecttimers = (); #the key is the name of the effect the value is the duration of the effect
my %MaxEffecttimers = (); #stores the values from the effects command so when you cast a spell it shows up in your effects

my %DMG_TYPE_ESO = (
	'Internal' => 1, 'Vile' => 1, 'Sacred' => 1, 'Psionic' => 1, 'Ectoplasmic' => 1
);
my @DAMAGETYPES = ("Physical", "Acid", "Electrical", "Fire", "Cold", "Sonic", "Magical", "Divine", "Positive", "Negative", "Internal", "Vile", "Sacred", "Psionic", "Ectoplasmic");
my @DAMAGETYPESIMM = ("Bludgeoning", "Piercing", "Slashing", "Acid", "Electrical", "Fire", "Cold", "Sonic", "Magical", "Divine", "Positive", "Negative");
my @COLS = ("orange", "#2160fe", "yellow", "white", "darkgray", "pink", "green", "red", "lightblue", "purple", "maroon","magenta","LightGoldenrod","DarkSeaGreen","DarkRed");


# added short names for damage types (for use of hgdata.xml)
my %COLOURS = ("Physical" => "orange",
                   "Bludgeoning" => "orange",
                   "Slashing" => "orange",
                   "Piercing" => "orange",
                   "Acid" => "green",
                   "Electrical" => "#2160fe",
                   "Elec" => "#2160fe", # hgdata.xml
                   "Fire" => "red",
                   "Cold" => "lightblue",
                   "Sonic" => "orange",
                   "Magical" => "pink",
                   "Divine" => "yellow",
                   "Positive Energy" => "white",
                   "Positive" => "white",
                   "Pos" => "white", # hgdata.xml
                   "Negative Energy" => "darkgray",
                   "Negative" => "darkgray",
                   "Neg" => "darkgray", # hgdata.xml
                   "Internal" => "maroon",
                   "Vile" => "magenta",
                   "Sacred" => "LightGoldenrod",
                   "Psionic" => "DarkSeaGreen",
                   "Ectoplasmic" => "DarkRed");

#
# List of mobs not to hit as they deal massive party kickback
my %DONOTHIT = ("Infernal Machine" => 1, 
		"Hellfire Engine" => 1,
		"Mammon's Tears", => 1,
		"Dolorous Tear" => 1,
		"Pyrexic Fume" => 1,
		"Phlogiston Ferment" => 1,
		"Coldforge Construct" => 1,
		"Rimeforged Assembly" => 1,
		"Malefic Wind" => 1,
		"Effluviarch" => 1,
		"Living Cold" => 1,
		"Fell Mistral" => 1);

#
# List of para monsters
# This list is used to register the percentage of paragon monsters encountered in hells
my %PARAMONSTERS = ("Algid Reaver" => 1,
		    "Aspirant of the Eight" => 1,
		    "Ayperobos Horde" => 1,
		    "Barbazu Razor" => 1,
		    "Bezekira Prideleader" => 1,
		
		    "Brachina Seductrix" => 1,
		    "Camizu" => 1,
		    "Cereberean Hound" => 1,
		    "Chosen of Tiamat" => 1,
		    "Cinderscale broodmother" => 1,
		    "Cloacal leech" => 1,
		    "Cornugon Taskmaster" => 1,
		    "Dolorous Tear" => 1,
		    "Effluviarch" => 1,
		    "Elder Nag" => 1,
		    "Elder Sahuagin" => 1,
		    "Ephasiarch" => 1,
		    "Erinyes Vitiarch" => 1,
		    "Excruciarch Inquisitor" => 1,
		    "Fell Mistral" => 1,
		    "Fen Render" => 1,
		    "Firstborn" => 1,
		    "Gelidarch" => 1,
		    "Hamatula Scourge" => 1,
		    "Hellfire Engine" => 1,
		    "Hellion" => 1,
                    "Hyperborean Fiend" => 1,
		    "Inchoate Baatorian" => 1,
		    "Infestiarch" => 1,
		    "Kyton Legionnaire" => 1,
		    "Magebane" => 1,
		    "Masterwork Baatorian Steel Golem" => 1,
		    "Minauron Rotscale" => 1,
		    "Orthon Fist" => 1,
		    "Phlogiston Ferment" => 1,
		    "Rachugon" => 1,
		    "Raja" => 1,
		    "Ravening Malebranche" => 1,
		    "Rimeforged Assembly" => 1,
		    "Spiniarch" => 1,
		    "Spoliated Ichor" => 1,
		    "Swarm Master" => 1,
		    "Unbound" => 1,
		    "Vexiarch" => 1);

# Add the P2 and P3 paragon monster names
foreach $_ (keys (%PARAMONSTERS)) {
    $PARAMONSTERS{"Superior " . $_} = 2;
    $PARAMONSTERS{"Elite " . $_} = 3;
    if ($DONOTHIT{$_}) {
	$DONOTHIT{"Superior $_"} = 1;
	$DONOTHIT{"Elite $_"} = 1;
    }
}


#
# This hash holds the immunities printed in the GUI
#
my %immunities = ("Bludgeoning" => "--",
		  "Piercing" => "--",
		  "Slashing" => "--",
		  "Magical" => "--",
		  "Acid" => "--",
		  "Cold" => "--",
		  "Divine" => "--",
		  "Electrical" => "--",
		  "Fire" => "--",
		  "Negative" => "--",
		  "Positive" => "--",
		  "Sonic" => "--"
);
my %resists = ();

my @IMMUNE = ("Critical Hits", "Sneak Attacks", "Mind Affecting Spells", "Bigby's Grasping Hand");

#
# This lists the default options
# These are replaced by the options listed in yal.cfg if that exists
#
my %OPTIONS = ("font" => "Times",
	       "fontsize" => 9,
	       "font-hit" => "Courier",
	       "fontsize-hit" => 9,
	       "font-resist" => "Times",
	       "fontsize-resist" => 9,
	       "savelogs" => 0,
               "badboy" => 1,
               "hitcounter" => 0, 
               "fixscroll" => 0,
	       "fuguebeep" => 0,
	       "showdamageheaders" => 1,
	       "verticalsummary" => 0,
	       "geometry" => "",
	       "ownspells" => 1,
	       "otherspells" => 1,
	       "sppercent" => 1,
	       "dcpercent" => 1,
	       "showstatchecks" => 1,
	       "catchtoonname" => 1,
	       "showparagons" => 1,
	       "hellentrymessagebox" => 1,

		# new options added by Separ
		'skipunknownspells' => 1,
		'showmonsterrace' => 0,
		'showmonsterflags' => 0, # boss-type, paragon level and do-not-hit
		'showmonsterheal' => 1, # which damage types heal a mob
		'showesotericdmg' => 'full', # no|full|sum
		'autostartrun' => 0 # if set automically log run to currentrun.txt
	       );


my $col_cold = "LightBlue3";
my $col_fire = "Red1";
my $col_acid = "Green1";


#---------------------------------------------------
#
#
# Now comes the GUI setup
#
#
#---------------------------------------------------

# Main Window
my $mw = new MainWindow();
$mw ->title("NWN logger v" .$version . ". --- by Claus Ekstrom 2008. Edits by Illandous & Separ");

#
# Now define the main frames/areas of the GUI
# The GUI is split into 3 areas: a panel on the rhs and the "main" bit which is split into an upper and lower panel
#
my $frm_top = $mw -> Frame();
my $frm_bottom = $mw -> Frame(-label=>"Spell/turning resists and saves");
my $frm_menu = $mw -> Frame(-relief=>'raised', -borderwidth=>2)  -> pack(-side=>'top', -fill=>'x');


# Set up the menu bar
my $menu_view = $frm_menu -> Menubutton(-text=>'View', 
					   -underline=>0,
					   -tearoff => 'no',
					   -menuitems => [['command' => "Party ~summary",
							   -command => \&dialog_party_summary],
							  ['command' => "~Detailed overview",
							   -command => \&dialog_detailed_summary],
							  ['command' => "~Effects",
							   -command => \&dialog_effects],
							  ['command' => "~Chat log",
							   -command => \&dialog_chat_log],
							  ]) -> pack(-side=>'left');

my $menu_party = $frm_menu -> Menubutton(-text=>'Party',
					 -underline=>0,
					 -tearoff => 'no',
					 -menuitems => [['command' => "~Party setup",
							 -command=>\&dialog_party_entry],
							['command' => "~Clear party",
							 -command=>\&clear_party]]) -> pack(-side=>'left');


my $menu_options = $frm_menu -> Menubutton(-text=>'Options', 
					   -underline=>0,
					   -tearoff => 'no',
					   -menuitems => [['command' => "~Preferences", 
							   -command => \&dialog_program_options],
							  [Separator => ''],
							  ['command' => "~Reset all stats", 
							   -command => \&reset_all]]) -> pack(-side=>'left');

my $menu_file = $frm_menu -> Menubutton(-text=>'File', 
					-underline=>0,
					-tearoff => 'no',
					-menuitems => [['command' => "Save ~HTML summary",
							-command => \&html_summary],
						       [Separator => ''],
							['command' => "~Start a run",
							 -command => \&runlog_start],
						       ['command' => "E~nd run",
							 -command => \&runlog_end,
							 -state => 'disabled'],
						       ['command' => "~Parse old log file", 
							-command => \&parse_old_log_file],
						       ['command' => "Save ~inventories", 
							-command => \&save_inventories]
						       ]) -> pack(-side=>'left');

## Top info frame: name, current server, uptime, logfile info
my $frm_info = $frm_top -> Frame();
$frm_info -> pack(-side=>'top', -anchor=>'w', -fill=>'x');
my $frm_name = $frm_info -> Frame() ->pack(-side=>'top');
my $toon_name = $frm_info -> LabEntry(-textvariable => \$toon,
				    -label => "Name",
				    -labelPack => [-side => 'left']) -> pack(-side=>'left');
my $newlog     = $frm_info -> Button(-text => "Next", -command =>\&inc_logcount, -padx => 3, -pady => 1)->pack(-side=>"right");
my $frm_logfile = $frm_info -> Frame() ->pack(-side=>'top');
my $logfile_text = $frm_info -> LabEntry(-textvariable => \$logfile_info,
				    -label => "Log:",
				    #-width => 5, # increase if we want to show seconds
				    -state => 'disabled', -disabledforeground => 'black',
				    -labelPack => [-side => 'left']) -> pack(-side=>'right');
my $top_info_area = $frm_info -> Text(-width=>60, -height=>1, 
				    -foreground=>'white', -background=>'black',
				    -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}])->pack(-side=>"top", -fill=>"x", -expand=>0);


## Fugue timers
my $frm_rightbar  = $mw -> Frame();
my $frm_killdeath = $frm_rightbar -> Frame(-relief=>'groove', -borderwidth=>2, -background=>"black") -> pack(-side=>'bottom', -fill=>'x');
my $frm_othertimers= $frm_rightbar -> Frame(-label=>"Timers", -relief=>'groove', -borderwidth=>2, -background=>"black") -> pack(-side=>'bottom', -fill=>'x');
my $othertimers = $frm_othertimers-> Scrolled('Text', -width=>17, -height=>8, 
				       -foreground=>'white', -background=>'black',
				       -scrollbars=>'s', -wrap=>'none', -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]) -> pack(-side=>'bottom', -fill=>'both', -expand=>1);
$othertimers->tagConfigure("none", -foreground => "red");
$othertimers->tagConfigure("dispelled", -foreground => "orange");
$othertimers->tagConfigure("casting", -foreground => "blue");

my $frm_dynamicwindow = $frm_rightbar -> Frame(-label=>"Hit Counter", -relief=>'groove', -borderwidth=>2);
$frm_dynamicwindow -> Label(-textvariable => \$hits, -foreground=>$col_cold, -background=>"black") ->pack(-fill =>'x');

my $frm_dynamicdamageheaders = $frm_rightbar -> Frame(-label=>"Hit Counter", -relief=>'groove', -borderwidth=>2);
$frm_dynamicdamageheaders -> Label(-textvariable => \$hits, -foreground=>$col_cold, -background=>"black") ->pack(-fill =>'x');

my $frm_fugue     = $frm_rightbar -> Frame(-label=>"Fugue timers", -relief=>'groove', -borderwidth=>2) -> pack(-side=>'top', -fill=>'both', -expand=>1);

my $fuguetimers = $frm_fugue->Scrolled('Text', -width=>17, -height=>10, 
				       -foreground=>'white', -background=>'black',
				       -scrollbars=>'s', -wrap=>'none', -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]) -> pack(-side=>'top', -fill=>'both', -expand=>1);

$fuguetimers->tagConfigure("critical", -foreground => "red");
$fuguetimers->tagConfigure("warning", -foreground => "pink");
# use other colors for our own toon so we better see it
$fuguetimers->tagConfigure("self", -foreground => "yellow");
$fuguetimers->tagConfigure("criticalself", -foreground => "black", -background => 'red');
$fuguetimers->tagConfigure("warningself", -foreground => "red");

#start ills hacking                                                                       _______________


## Character status
my $frm_char = $mw -> Frame(-relief=>'ridge', -borderwidth=>2);

my $frm_kills     = $frm_killdeath -> Frame(-label=>"Kills:", -relief=>'groove', -borderwidth=>2, -background=>"black") -> pack(-side=>'top', -fill=>'x');
my $frm_deaths    = $frm_killdeath -> Frame(-label=>"Deaths:", -relief=>'groove', -borderwidth=>2) -> pack(-side=>'top', -fill=>'x');
$frm_kills -> Label(-textvariable => \$kills, -foreground=>$col_acid, -background=>"black") ->pack();
$frm_kills -> Label(-textvariable => \$lastkilled, -foreground=>"white", -background=>"black") ->pack();

$frm_deaths -> Label(-textvariable => \$deaths, -foreground=>$col_fire) ->pack();
$frm_deaths -> Label(-textvariable => \$lastkiller) ->pack();


my $conceal_lab = $frm_char -> Label(-text => "Conceal");

my $saves   = $frm_bottom -> Scrolled('Text', -width=>80, -height=>4, 
				      -foreground=>'white', -background=>'black',
				      -font => [-family => $OPTIONS{"font-resist"}, -size=>$OPTIONS{"fontsize-resist"}],
				      -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'right', -fill=>'both', -expand=>1);
my $resists = $frm_bottom -> Scrolled('Text', -width=>60, -height=>4, 
				      -foreground=>'white', -background=>'black',
				      -font => [-family => $OPTIONS{"font-resist"}, -size=>$OPTIONS{"fontsize-resist"}],
				      -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'right', -fill=>'both', -expand=>1);


$resists->tagConfigure("darkgray", -foreground => "darkgray");
$resists->tagConfigure("lightblue", -foreground => "lightblue");
$resists->tagConfigure("yellow", -foreground => "yellow");
$resists->tagConfigure("red", -foreground => "red");
$resists->tagConfigure("green", -foreground => "green");
$othertimers->tagConfigure("casts", -foreground => "orange");
$saves->tagConfigure("lightblue", -foreground => "lightblue");
$saves->tagConfigure("yellow", -foreground => "yellow");


#$resist -> Subwidget("text") -> tagConfigure("darkgray", -foreground => "darkgrey");

#
# Make a dummy label
#
my $frm_inc = $frm_top -> Frame(-label => "Incoming damage:") -> pack(-side=>"top", -anchor=>"w", -fill=>"both", -expand=>1);
my $frm_out = $frm_top -> Frame(-label => "Outgoing damage:") -> pack(-side=>"top", -anchor=>"w", -fill=>"both", -expand=>1);

my $hits_inc = $frm_inc -> Scrolled('Text', -width=>35, -height=>6, 
				      -foreground=>'white', -background=>'black',
				      -tabs => [$OPTIONS{"fontsize-hit"}*5], # screen distance sucks on my laptop -tabs => [qw/.3i/],
				      -font => [-family => $OPTIONS{"font-hit"}, -size=>$OPTIONS{"fontsize-hit"}],
				      -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'left', -fill=>"both", -expand=>1);

my $frame_inc_header = $frm_inc -> Frame() -> pack(-side=>'right', -fill=>"both", -expand=>1);

my $dmgheader_inc = $frame_inc_header -> Text(-width=>60, -height=>1, 
				      -foreground=>'white', -background=>'black',
				      -tabs => [$OPTIONS{"fontsize"}*3.5], # screen distance sucks on my laptop -tabs => [qw/.35i/],
				      -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}])->pack(-side=>"top", -fill=>"x", -expand=>0);

my $damage_inc = $frame_inc_header -> Scrolled('Text', -width=>60, -height=>6, 
				      -foreground=>'white', -background=>'black',
				      -tabs => [$OPTIONS{"fontsize"}*3.5], # screen distance sucks on my laptop -tabs => [qw/.35i/],
				      -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}],
			              -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'top', -fill=>"both", -expand=>1);

my $hits_out = $frm_out -> Scrolled('Text', -width=>35, -height=>6, 
				      -foreground=>'white', -background=>'black',
				      -tabs => [$OPTIONS{"fontsize-hit"}*5], # screen distance sucks on my laptop -tabs => [qw/.3i/],
				      -font => [-family => $OPTIONS{"font-hit"}, -size=>$OPTIONS{"fontsize-hit"}],
				      -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'left', -fill=>'both', -expand=>1);

my $frame_out_header = $frm_out -> Frame() -> pack(-side=>'right', -fill=>"both", -expand=>1);
my $dmgheader_out = $frame_out_header -> Text(-width=>60, -height=>1, 
				      -background=>'black',
				      -tabs => [$OPTIONS{"fontsize"}*3.5], # screen distance sucks on my laptop -tabs => [qw/.35i/],
				      -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}])->pack(-side=>"top", -fill=>"x", -expand=>0);

my $damage_out = $frame_out_header -> Scrolled('Text', -width=>60, -height=>6, 
				      -foreground=>'white', -background=>'black',
				      -tabs => [$OPTIONS{"fontsize"}*3.5], # screen distance sucks on my laptop -tabs => [qw/.35i/],
				      -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}],
			              -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'top', -fill=>"both", -expand=>1);

# Now insert the headers _if_ the headers are desired
$dmgheader_inc -> insert('end', "Tot\t", "white");
$dmgheader_out -> insert('end', "Tot\t", "white");
foreach $_ (@DAMAGETYPES) {
    $dmgheader_inc -> insert('end',  substr($_,0,3) . "\t",  "$COLOURS{$_}");
    $dmgheader_out -> insert('end',  substr($_,0,3) . "\t",  "$COLOURS{$_}");
}



##
my $frm_status = $mw -> Frame();
# logfile info moved to top right
#my $newlog     = $frm_status -> Button(-text => "New Log File", -command =>\&inc_logcount)->pack(-side=>"right");
my $imms       = $frm_status -> Text(-background=>"black", -height=>1, width=>70, -tabs => [qw/.23i/],
				     -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]) -> pack(-side=>"right");
my $status     = $frm_status -> Label(-textvariable => \$statusmessage, -borderwidth=>2, -relief=>'groove', -anchor=>"w") ->pack(-side=>"left", -fill => 'x', -expand=>1);


##
## Geometry management
##
$frm_status -> pack(-side=>'bottom', -anchor=>'w', -fill=>'x');
$frm_rightbar  -> pack(-side=>"right", -fill => 'y', -anchor=>'n');
$frm_top    -> pack(-side=>'top', -expand=>1, -fill => 'both');
$frm_bottom -> pack(-side=>'top', -expand=>1, -fill => 'both');



my $parsetimer = $mw->repeat($parsetime => \&parse_log_file);
# This is really a poor mans version of the timers. A potential problem is the time NWN takes to write stuff to the log - espcially on network drives
# It would be much smarter to continuously adjust the timers according to the log time. I may get around to that at some point
my $rpdeathtimers = $mw->repeat(1000 => \&update_death_timers);   
my $rpeffectstimers = $mw->repeat(1000 => \&update_effects_timers);

#
# Make sure that the party selection page is listed when the program starts
#
# $mw->after(1 => \&dialog_party_entry);



#
#
# Done with GUI setup
#
#

#------------------------------------------------
# 
# Main bit of program
#
#------------------------------------------------

load_configuration();
dialog_chat_log();   # Setup the chat log 
configure_fonts();   
import_hgdata_xml(); # import hgdata.xml
print_immunities();
if ($OPTIONS{'autostartrun'}) {
    runlog_start('currentrun.txt');
}


open(LOGFILE, "$currentlogfile");

MainLoop;
# save_configuration();
close(LOGFILE);


#------------------------------------------------
# 
# End of program
#
#------------------------------------------------


#
# This is the main rutine parsing the log file
#
sub parse_log_file {

    return if !(-e $currentlogfile);

    # Make sure we're parsing the active log file

    # logfile- and run-info is now top-right
    $logfile_info = $currentlogfile . (defined($saverunbuffer) ? ' (RUN)' : '');

    #$statusmessage .= " | Total XP: " . $totalxp . " | Total dmg: " . (defined($damage_done{$toon}) ? $damage_done{$toon} : "None yet" ) ;
    $statusmessage = "Total XP: " . $totalxp . " | Total dmg: " . (defined($damage_done{$toon}) ? $damage_done{$toon} : "None yet" ) ;

    if ($OPTIONS{"showparagons"}==1) {
	if ($totalmobkills>0) { 
	    
	    my $numberofparagons = (exists($paracount{1}) ? $paracount{1} : 0) + (exists($paracount{2}) ? $paracount{2} : 0) + (exists($paracount{3}) ? $paracount{3} : 0);
	    $statusmessage .= " | Paragons: " . int($numberofparagons/$totalmobkills *1000)/10 . "%";
	}
	else {
	    $statusmessage .= " | Paragons: 0%";
	}
    }
        
    my $endhitout = ($hits_out -> yview())[1];
    my $endhitinc = ($hits_inc -> yview())[1];
    my $enddmgout = ($damage_out -> yview())[1];
    my $enddmginc = ($damage_inc -> yview())[1];
    my $endsaves  = ($saves -> yview())[1];
    my $endresists= ($resists-> yview())[1];

    # Clear the EOF flag
    seek(LOGFILE,0,1) || ($statusmessage .= " | Log file not found!");
    while(<LOGFILE>) {
	if (defined($saverunbuffer)) {
	    $saverunbuffer .= $_ ;
	}

	if (/^\s*$/) { # skip empty lines
	    parse_sm_end() if $parse_sub_mode;
		next;
	}

	# Remove DOS line shifts if any. Old habit
	s/\015\012/\012/;
	# drop the initial bit
	s/\[CHAT WINDOW TEXT\]\s+//;
	s/^\[([^\]]+)\]\s//;
	my $time = $1 if defined $1;

	# update server uptime if we did catch it once
	if ($time // 0) {
	    my $new_time = str2time($time) || 0;
	    $log_start_ts = $new_time if !$log_start_ts; # remember first parsed timestamp
	    if ($new_time != $srv_time) {
		# current second actually changed
		$srv_time = $new_time;
		#print "$time -> " . str2time($time) . ", uptimeat|\n" if ($time);
		if ($uptime_secs) {
		    $server_uptime = $uptime_secs + ($srv_time - $uptimeat);
		    my $current_round = int $server_uptime / 6;
		    update_top_info_area();
		    if ($current_round != $server_round) {
			# every 6 seconds we have a new round
			#printf "new round: %d -> %d @ %d - %s\n", $server_round, $current_round, $server_uptime, time2str("%R", $server_uptime, 0);
			$server_round = $current_round;
		    }
		}
	    }

	    # if we got a timestamp all parsing submodes are finished
	    parse_sm_end(); # $parse_sub_mode = '';
	}
	elsif (/^  / && $parse_sub_mode) {
		# data to collect from an info command if starting with '  ' (2 blanks)
		next if parse_log_submode();
	}

	# Remove chats and stuff
	next if parse_chat_line();

	#
	# Match on most frequent lines first and use next (instead of a lot of else if's) to speed up evaluations
	# 


	# combat: attack and damage, xp and kills
	next if parse_combat_line();

	   #effects
	   #if (/^    \#(\d+) (.+) \[(.+)\]/) {
	   #ills effects
	   if(/^    \#(\d+) (.+) \[((\d+)[m])?(\d+)[s].+\]/) {
	   my $tempetimer = ($4 * 60) + $5;
	   my $tempeid=$1;
	   my $tempename= $2;
	   #no longer required
	   #push(@{$etimers{$tempetimer}}, $tempename);
	   #removes the old one if it exists, and then puts the new one in place
	   if (exists $Effecttimers{$2}){
			delete $Effecttimers{$2}
			 
		}
	   $Effecttimers{$tempename} = $tempetimer;
	   $MaxEffecttimers{$tempename} = $tempetimer;
	   }

       # Different timers. Missing a lot of stuff here. Imm force for example
       # GR
       if (/^Greater Sanctuary will be available again in 150 seconds/) {
	   start_timer(\@grtimer, 150);	   
	   next;
       }
       if (/Greater Smite will be available again in (\d+) seconds/) {	   
	   start_timer(\@gstimer, $1) if ($1 >=120);  # Make sure only to start timer if it's the first occurrence
	   next;
       }


       # Saves, skill and ability checks
       if (/^(.+) : (Strength|Dexterity|Constitution|Intelligence|Wisdom|Charisma) vs. (.+) : \*(success|failure|success not possible)\* : .+ vs\. DC: (\d+)/) {
	   $AbilityChecks{$3}{$2} = $5;
           $saves -> insert('end',$_, 'lightblue');
	   next;
       }
       if (/^(.+) : (Will|Fortitude|Reflex) Save : /) {
           $saves -> insert('end',$_, 'white');
	   next;	   
       }
       if (/^(.+) : (Will|Fortitude|Reflex) Save vs. (.+) : \*(success|failure)\* : \(\d+ \+ (\d+) = \d+ vs\. DC: (\d+)\)$/) {
	   if ($toon eq $1) {
	       $saves -> insert('end',$_, 'white');
	   }
	   else {
	       chomp;
	       $saves -> insert('end',$_, 'lightblue');
	       if ($OPTIONS{"dcpercent"}==1) {
		   $saves -> insert('end', " (" .((max(1, min(20, (($6-1) - $5)))))*5 . "%)"."\n", 'yellow');
	       }
	       else {
		   $saves -> insert('end',"\n");
	       }
	   }
	   $Saves{$1}{$2}{"min"}{$3} = $5 if (!exists($Saves{$1}{$2}{"min"}{$3}));
	   $Saves{$1}{$2}{"max"}{$3} = $5 if (!exists($Saves{$1}{$2}{"max"}{$3}));
	   $Saves{$1}{$2}{"min"}{$3} = $5 if $5 < $Saves{$1}{$2}{"min"}{$3};
	   $Saves{$1}{$2}{"max"}{$3} = $5 if $5 > $Saves{$1}{$2}{"max"}{$3};
	   next;	   
       }
       if (/^(.+) : (Discipline|Concentration|Taunt|Bluff) vs. (.+) : \*(success|failure|success not possible)\* : .+ vs\. DC: (\d+)/) {
	   $SkillChecks{$3}{$2} = $5;
	   if ($toon eq $1) {
	       $saves -> insert('end',$_, 'white');
	   }
	   else {
	       $saves -> insert('end',$_, 'lightblue');
	   }
	   next;	   
       }


       # Skills
       if (/^$toon : (.+) vs\. (.+) : \*(success|failure)\* : /) {
           $saves -> insert('end',$_, 'yellow');
	   next;
       }


       # Spell and turning resists
       # Never got round to including turn resists
	if (/^(.+) casts (.+)$/) {
            my $who = $1;
	    if ($2 =~ /unknown spell/) {
		next if $OPTIONS{'skipunknownspells'};
		if ($OPTIONS{"otherspells"} && ($who ne $toon)){  
		    $resists -> insert('end',$_, 'darkgray');
		}
	    }
	    else {
		if ($OPTIONS{"ownspells"} && ($1 eq $toon)) {
		    #make sure it is a effect that we have seen
			if (exists $MaxEffecttimers{$2}){
			$Effecttimers {$2} = $MaxEffecttimers{$2};
			}
			$resists -> insert('end',$_, 'casts');
		}
		elsif ($OPTIONS{"otherspells"} && ($1 ne $toon)){  
		    $resists -> insert('end',$_, 'white');
		}
	    }
	    next;
	}	
	next if (/^(.+) casting (.+)$/);

       # Spell penetration
       if (/^(.+) : Spell Penetration : \*(success|failure)\* : \((\d+) \+ (\d+) .+ vs. SR: (\d+)\)$/) {
	   $resists -> insert('end', "SP: $1 : ", 'lightblue');
	   if ($2 eq "success") {
	       $resists -> insert('end', "*$2*", 'green');
	   }
	   else {
	       $resists -> insert('end', "*$2*", 'red');
	   }
	   $resists -> insert('end', " : $3 + $4 = " . ($3 + $4) . " vs. SR: $5 ", 'lightblue');
	   # List the spell penetration percentage if that is desired
	   if ($OPTIONS{"sppercent"}==1) {
	       $resists -> insert('end', "(" .(21 - (max(1, min(20, ($5 - $4)))))*5 . "%)"."\n", 'yellow');
	   }
	   else {
	       $resists -> insert('end', "\n");
	   }
	   
	   if (exists($SR{$1})) {
	       $SR{$1} = $5 if ($5>$SR{$1});
	   }
	   else {
	       $SR{$1} = $5;
	   }
	   next;	   
       }

       if (/^(.+) : Spell Resistance : \*(defeated|success)\* : (.+)$/) {
           $resists -> insert('end',$_, 'lightblue');
	   next;
       }

       # Turning
       if (/^(.+) : Turn (Outsider|Construct|Vermin|Undead) : \*(success|failure)\* : \((\d+) \+ (\d+) .+ vs. TR: (\d+)\)$/) {
	   $resists -> insert('end', "Turn $2: $1 : *$3* : ($4 + $5 = " . ($4 + $5) . " vs. SR: $6 (" . (21 - (max(1, min(20, ($6 - $5)))))*5 . '%)'."\n", 'lightblue');
	   
	   if (exists($TR{$1})) {
	       $TR{$1} = $5 if ($6>$TR{$1});
	   }
	   else {
	       $TR{$1} = $5;
	   }
	   next;	   
       }
	
	# Spell and condition immunity
	# Need two here as they are listed differently in the log
	#if (/^(.+) : Immune to (.+)\.$/) {
	if (/^(.+) : Immune to (.+)\.?$/) {
	    $immune{$1}{$2} = 1;
	    # TODO: display somewhere if $1 is our current target
	    next;
	}
	#if (/^(.+) : Immune to (.+)$/) {
	#    $immune{$1}{$2} = 1;	    
	#    next;
	#}	

	# more output from !list imm
	if (/^(Spell|Other) immunities:$/) {
		$parse_sub_mode = "imm$1";
	}

	#
        # Various lines that cannot really be used for anything as you cnnot see who causes them
        #
	if (/^\* (Mortal Strike|Called Shot|Penetrating Strike) \*$/) {
	    next;
	}

	#
	# Clear fugue timer when you didn't really die
	#
	if (/An illusion of life forms around you, then dissipates, taking your place in the beyond!/) {
	    clear_last_fugue_timer();
		%Effecttimers = ();
	    next;
	}
	if (/Your Eternal Return spell fires, preventing the life from leaving your body!/) {
	    clear_last_fugue_timer();
		%Effecttimers = ();
	    next;
	}



	# meta-data (server, party members, ...)
	next if parse_collect_metadata();

	#ills dispelelling routine
	#if (/^.+\*dispelled\*.+$/){
	if (/^(.+) : Dispel (.+) : \*dispelled\* :(.+)$/){
	   	
	   if ($toon eq $1) {
			$resists -> insert('end',"Your $2 has been dispelled \n", 'orange');
			#print "your $2 dispelled \n";
			#print $Effecttimers{$2};
			delete $Effecttimers{$2};

		}

		next;
	}

	#
	# Effects 
        #
	# This one registers who the effects concern and clears effects timers so they can be regenerated
	if (/^\[Server\] Effects on (.+):/) {
		%Effecttimers = ();
		
	    $effectid = $1;
	    $effectid = $toon if ($1 eq "you");
	    next;
	}

	if (/^    \#(\d+) (.+) \[(.+)\]/) {
	    # This only work on yourself atm
	    $Effects{$effectid}{($2 . " " . $1)} = $3;
	    next;
	}

	# check if a list of gear follows
	next if parse_gear_list_header();

	# Loot split rolls for whiners. Not sure what I will do with it yet
	if (/(.+) rolled a \[D(4|6|8|10|12|20|100)\] and got a: \[(\d+)\]\./) {
	    
	}	

	# Clear all effects timers after rest
	if (/^Done resting\.$/) {
		%Effecttimers = ();
	}

	# Messages regarding entering and leaving the server
	#next if (/(.+) has left as a player\.\./);
	#next if (/(.+) has joined as a player\.\./);
	next if (/(.+) has (joined|left) as a player\.\./);

	# area specific lines - for now only hells
	# TODO: if ($current_area =~ /^Hells/)
	next if parse_line_area_Hells();

        # Yay!
        if (/You are flooded with an incredible sense of well-being!/) {           
	    $saves -> insert('end',$_, 'yellow');
	    $shamelessadvertising = 1;
            next;
        }

        # Grab the uses lines
        if (/^(.+) uses (.+)$/) {
            next;
        }

	#
	# Starting hell run
	# 
	if (/\Q$toon\E: Send me to (Dis|Minauros|Phlegethos|Stygia|Malbolge|Maladomini|Cania|Nessus)/) {
	    if ($OPTIONS{"hellentrymessagebox"}==1) {
		my $clear_stats = $mw->messageBox(-message => "Clear stats?",
						  -title => "Entering hells",
						   -type => "yesno", -icon => "question");		
		if ($clear_stats eq "Yes") {
		    reset_all();
		} 
	    }
	    next;
	}

	#
	# Different ingame commands to control program
	#
	next if parse_player_cmds();

	# TODO: some more things we could catch and display in info area
	# if (/You are in Higher Ground Enhanced Mode./)
	# if (/Latest Module Build: 2009-07-27/)
	if ($time && s/^\[Server\] //) {
	    parse_srv_msg($_);
	    next;
	}


	print "Line not parsed : $_" if ($debug ne 0);
    }

    if ($OPTIONS{"fixscroll"} == 1) {
	$resists->see('end');
	$saves->see('end');
	$hits_out->see('end');
	$hits_inc->see('end');
	$damage_out->see('end');
	$damage_inc->see('end');
    }

    # Always scroll to bottom if the window was at bottom before. Bugs under windows?    
    $resists->see('end') if $endresists == 1;
    $saves->see('end')  if $endsaves == 1;
    $hits_out->see('end') if $endhitout == 1;
    $hits_inc->see('end') if $endhitinc == 1;
    $damage_out->see('end') if $enddmgout == 1;
    $damage_inc->see('end') if $enddmginc == 1;

    # Check if it's time to change log files
    check_log_file();
}

# chat log
sub parse_chat_line {
    if (/^(.+ )(.*): \[(Tell|Party|Shout)\] /) {
	my ($fname, $sname, $type) = ($1, $2, $3);
	my $speakername = $fname . $sname;
	# Now remove the silly space that is added to toons with no last name
	chop($speakername) if ($sname eq "");

	if ($type eq ("Tell")) {
	    # strip the colour code for guild chats
	    s/<c.+?>//g;
	    s/<\/c.*?>//g;
	    if (/\[Guild\]/) {
		s/^.*\[Tell\] //;
		$chatlog->insert('end', $_, 'purple');
	    }
	    elsif (($speakername =~ /^\s*$/) && /Interserver (\w+) message from (.*) \((.*)\): (.*)/) {
		my %channelcolors = ('newbie' => 'darkgray', 'bazaar' => 'red');
		$chatlog->insert('end', "$2 ($3)");
		$chatlog->insert('end', "[".ucfirst($1)."]: $4\n", $channelcolors{$1});
	    }
	    else {
		$chatlog->insert('end', $_, 'green');
	    }

	}
	elsif ($type eq ("Shout")) {
	    if (($speakername eq 'SERVER') && /Run forming on( this)? server( \d+)?\. Contact (.*) \((.*)\) if interested: (.*)/) {
		my ($toon, $player, $srv, $msg) = ($3, $4, $2 // '', $5);
		$srv =~ s/^ /@/ if $srv;
		$chatlog->insert('end', "$toon ($player)$srv");
		$chatlog->insert('end', "[RUN]: $msg\n", 'orange');
	    } else {
		$chatlog->insert('end', $_, 'yellow');		
	    }
	}
	else {
	    $chatlog->insert('end', $_);
	    # Remember to code this person as a potential party member if in party talk
	    #to be taken out when list of players is defined
	    $listofplayers{$speakername} = 1 if (/\[Party\]/);
	}
	$chatlog->see('end');
	return 1;
    }

    return 0;
}

# combat: attack and damage lines, kills and xp
sub parse_combat_line {

	# Damage lines first as they are most abundant
	if (/(.+) damages (.+): (\d+) \((.+)\)/) {
	    my ($attacker, $defender, $total, $damages) = ($1, $2, $3, $4);

	    return 1 if hg_ignore_enemy($defender); # some things (like walls, doors, ...) should be ignored

	    $damage_done{$attacker} += $total;                   # sum for attacker
	    $damage_taken{$defender} += $total;                  # sum for defender
	    $TotalDamage{$attacker}{$defender} += $total;        # stores attacker and defender
	    
	    my $meleehit = 0;
	    $meleehit = 1 if ($damages =~ /\d+ Physical/); # TODO: find out if we catch bigby spells here

	    # get mob healing info if attacker is a party member
	    my $heals = exists($party{$attacker}) ? hg_mob_heals($defender) : 0;

	    # Now make sure to keep information about which damage types that are actually doing damage
	    # Stole this idea and code from Kins. Ty :)
	    my %damage_type = ();
	    while ($damages =~ s/(\d+) (\S+)\s*//) {
			my ($damount, $dtype) = ($1, $2);
			# TODO: if ($heals{$dtype}) ...
			$damage_type{$dtype} = $damount;
			$DamageTypesDealt{$attacker}{$dtype} = 1 if ($meleehit==1);
	#		print "Setting $attacker $dtype $DamageTypesDealt{$attacker}{$dtype}\n";		
			$dam_taken_detail{$defender . " :d: " . $dtype} += $damount;
	    }
	    
	    # General data was saved above
		# Now we should handle the specific damage data that is shown on the GUI
	    return 1 unless ($attacker eq $toon || $defender eq $toon);
	    
	    if ($toon eq $attacker) {
			append_dmg_line($damage_out, $total, \%damage_type, $defender, $heals);
	    }
	    else {
			append_dmg_line($damage_inc, $total, \%damage_type, $attacker, 0);
	    }
	    return 1;
	}
	
	# Attacks
	# Some attacks are still not matched. For example the manticore spike attacks
	if (/(.+ \: )?(.+) attacks (.+) : \*(hit|miss|critical hit|parried|target concealed: (\d+)%)\* : \((\d+) \+ (\d+)/) {
		#my ($attacker, $defender, $roll, $ab) = ($2, $3, $6, $7);
		my ($attacker, $defender, $status, $roll, $ab) = ($2, $3, $4, $6, $7);

		return 1 if hg_ignore_enemy($defender);

		#$status = $4;
		$status = "crit" if $status eq "critical hit";
		$status = $5."%" if (defined($5));

		process_attack($attacker, $defender, '', $roll, $ab, $status);
		return 1;
	}
	
	# Special attacks. Kept by themselves because they are less frequent
	# Flurry of blows still not matched !!
	if (/(.+ \: )?(.+) attempts (Cleave|Great Cleave|Knockdown|Improved Knockdown|Disarm|Improved Disarm|Melee Touch Attack|Ranged Touch Attack|Called Shot\: Arm|Called Shot\: Leg) on (.+) : \*(hit|miss|critical hit|parried|target concealed: (\d+)%|resisted)\* : \((\d+) \+ (\d+)/) {
		# print $_;
		#my ($attacker, $defender, $attacktype, $roll, $ab) = ($2, $4, $3, $7, $8);
		#$status = $5;
		my ($attacker, $defender, $attacktype, $status, $roll, $ab) = ($2, $4, $3, $5, $7, $8);
		$status = "crit" if $status eq "critical hit";
		$status = $6."%" if (defined($6));

		process_attack($attacker, $defender, $attacktype, $roll, $ab, $status);
		return 1;
	}

	# Kill
	if (/^(.+) killed (.+)$/) {
		$kills{$1}++;
		$deaths{$2}++;
		$partykiller{$2} = $1;
		$partykilled{$1} = $2;
		$Kills{$1}{$2}++;

		# Start death timer if it was the toon that died and clear effects timers
		if ($2 eq $toon) {
			$deaths++;
			$lastkiller = $1;
			%Effecttimers = ();
		} 
		if (exists($party{$2})) {
			# Start a death timer if it was a party member who died
			push(@{$timers{300}}, $2) unless $current_map && !$hg_maps{$current_map}{'respawn'};
		}
		else {
			# Check if the monster was a paragon
			$totalmobkills++;
			my $pl = hg_para_level($2);
			$paracount{$pl}++ if ($pl);
		}

		# Hmm. Still counting this separately for the player. That is not necessary. Should be integrated with the general hash
		if ($toon eq $1) {
			$kills++;
			$lastkilled = $2;
		}

		return 1;
	}    

	# XP
	if (/^Experience Points Gained:\s+(\d+)$/ ) {
		$totalxp += $1;
		return 1;
	}

	return 0;
}

#
# parse server msgs
# returns 1 if we had a match, otherwise 0
#
sub parse_srv_msg {
    chomp; # remove \n at end ... TODO: why was this not done earlier?

    # where are we?
    if (/^You are now in (.*) \((.*)\)\.$/) {
	my ($name, $pvp) = ($1, $2);
	
	if (exists($hg_maps{$name})) {
	    $current_area = $hg_maps{$name}{'area'} // ''; # default: no area
	} else {
	    $hg_maps{$name}{'new'} = 1;
	    $current_area = '';

	    my @parts = split(/ - /, $name);
	    if ($#parts) {
		if (exists($hg_areas{$parts[0]})) {
		    $current_area = $parts[0];
		}
		elsif ($parts[0] =~ /(Avernus|Dis|Minauros|Phlegethos|Stygia|Malbolge|Maladomini|Cania|Nessus)/) {
		    $current_area = $1;
		    $hg_areas{$1} = {area => 'Hells', new => 1};
		}
	    }

	    if (!$current_area) {
		@parts = split(/ /, $parts[0]); # $name);
		$current_area = $parts[0] if $#parts && exists($hg_areas{$parts[0]});
	    }

	    $hg_maps{$name}{'area'} = $current_area;
	}

	$current_map = $name;
	# remember pvp-status of map
	$hg_maps{$current_map}{'pvp'} = $pvp;

	# which run are we doing?
	$last_run = $current_area if $current_area;
    }

    # area status: fugue/limbo/... ?
    elsif (/^You will (.*) if you respawn in this area\.$/) {
	$hg_maps{$current_map}{'respawn'} = $1 if ($current_map);
    }

    # update demi count
    #elsif (/^The last spawn in this area was affected by (\d+) demi iterations\.$/) {
    #}

    # switch mode to collecting immunities
    elsif (/^Damage immunities:$/) {
	$parse_sub_mode = 'imm';
    }

    # !iteminfo
    #elsif (/^Properties of (.+):$/) {
    #}

    # !itemlevel
    #elsif (/^Requirements for (.+):$/) {
    #}

    # !list inventory
    #elsif (/^Your inventory:$/) {
    #}

    # get LBAB and CC
    #elsif (/^Legendary BAB: +(\d+) \(LWF \/ Control Class: ([\w ]+)\)$/) {
    #}

    # list of done quests
    #elsif (/^You have the following accomplishments:$/) {
	#$parse_sub_mode = 'acc'
    #}

    # !list ac
    #elsif (/^Armor class:/) {
    #}

    # !list saves
    #elsif (/^Saving throws:/) {
    #}

    else {
	return 0;
    }

    return 1;
}

#
# sub-mode parsing, collect data after a recognized header
# data-lines start with at least 2 blanks
#
sub parse_log_submode {
	if ($parse_sub_mode) {
		#print "submode parsing: $parse_sub_mode\n";
		my $fn = "parse_sm_$parse_sub_mode";
		# print "sub func found: $fn\n" if (defined(&$fn));
		goto &$fn if (defined(&$fn));
	}
	return 0;
}

# end of data for a sub-mode parser
sub parse_sm_end {
	if ($parse_sub_mode) {
		#print "submode end: $parse_sub_mode\n";
		my $fn = "parse_sm_end_$parse_sub_mode";
		goto &$fn if (defined(&$fn));
		$parse_sub_mode = '';
	}
}

#
# Immunities
# List immunities read from !list imm . Still some trouble with formatting
#

# collect data for "Damage immunities"
sub parse_sm_imm {
	#printf "in parse_sm_imm\(\)\n";
	#if (/^    (Bludgeoning|Piercing|Slashing|Magical|Acid|Cold|Divine|Electrical|Fire|Negative|Positive|Sonic): \.+(\d+)%(\.+(\d+)\/-\.+)?/)
	if (/^    (\w+): \.+(-?\d+)%(\.+(\d+)\/-\.+)?/) {
		#print "imm found: '$1'/'$2'/'".($4 // '?')."'\n";
		$immunities{$1} = $2;
		$resists{$1} = $4 // '';
		print_immunities(); # TODO: only once when we have all of them
	}
	return 1;
}

# collect data for "Other immunities"
sub parse_sm_immOther {
	if (/^    ([\w ,]+)/) {
		my @ilist = split(/, /, $1);
		$ilist[$#ilist] =~ s/^and // if ($#ilist);
		# TODO: save imms for display
		print "other imms: ". join(',', @ilist)."\n";
	}
	return 1;
}

# collect data for "Spell immunities"
sub parse_sm_immSpell {
	if (/^    Spells of level (\d) and lower/) {
		print "Spell immunity by level: $1\n";
	}
	elsif (/^    ([\w ,]+)/) {
		my @ilist = split(/, /, $1);
		$ilist[$#ilist] =~ s/^and // if ($#ilist);
		# TODO: save imms for display
	}
	return 1;
}

#######################################################################
# meta-data collecting (server, party, location, ...)

sub parse_collect_metadata {
	# If you use the PC Scry then set that toon as the primary
	if (/^(.+): PCScry: Select an option$/) {
		if ($OPTIONS{"catchtoonname"}==1) {
			new_party_member($1);
			$toon = $1;
		}
		return 1;
	}

	# Welcome message
	if (/Welcome to Higher Ground, (.+)!$/) {
		if ($OPTIONS{"catchtoonname"}==1) {
			# clear old toon from party if re-login with another toon
			$party{$toon} = 0 if ($toon and defined $party{$toon});

			new_party_member($1);
			$toon = $1;
		}
		return 1;
	}

	# !who header - clears party stats
	if (/^\[Server\] ===== Server (\d+).+$/){
		$parse_sub_mode = 'who';
		#%party = ();
		if ($1 eq $server) {
			$myserverwho = 1;
			clear_party() if $catchpartywho; # only if it's a party-who
		} else {
			$myserverwho = 0;
			$catchpartywho = 0;
		}
		return 1;
	}

	# On which server are we? - at welcome and end of !who
	if (/You are on server (\d+)/) {
	    $server = $1;
	    $myserverwho = 0; # no !who output to follow immediately after
	    $catchpartywho = 0;
	    return 1;
	}

	# prepare server uptime display
	if (/This server has been up for ((\d+) hours, )?(\d+) minutes,? and (\d+) seconds\./) {
	    $uptime_secs = $4 + 60*$3 + ($2 ? 3600*$2 : 0);
	    $uptimeat = $srv_time;
	    return 1;
	}

	if (/^(.+) has (joined|left) the party\./) {
		$listofplayers{$1} = 1;
		if ($2 eq "joined") {
			new_party_member($1); # TODO: make option for this catch
		} else {
			$party{$1} = 0;
		}
		return 1;
	}

	return 0;
}

# Player information from !who commands
sub parse_sm_who {
	return 1 if (!$myserverwho); # ignore playerlisting from other servers
	# old if (/^  \s*\[\d+(\/\d+)?\]( \|.+\|)? (.+) $/) {
	#ills version: if (/^.+\[(\d+ \D\D\D.+?)\] (.+) $/){    
	if (/^.+\[(\d+ \D\D\D.+?)\] (.+) $/) {
		#print "!who output: $_" if (1);
		#print "!who output: $_" if ($debug);
	    chomp;
	    # Remove DM tag
		if ($debug) {print "$_ in who output ";}
	    my $toonname = $2;
	    $toonname =~ s/ \[DM PC\]//;
	    # Remove guild tag
	    #removed, done with regex
		#$toonname =~ s/ <.+>//;

	    # Now this is a bit trickly and certanly not a perfect solution
	    # Remove things in end parentheses as they most likely are because of an area eg., !who 113 area.
	    # Some people use it to ID theis login through so lets see ....
		#due to the new maching routine, this next line no matter is required.
	    #$toonname =~ s/ \(.{8,30}\)//;
	    
	    $listofplayers{$toonname} = 0 if (!defined($listofplayers{$toonname}));
	    #$party{$toonname} = 1;
	    new_party_member($toonname) if ($catchpartywho);
		if ($debug) {print "$listofplayers{$toonname} \n";}
		
#	    print "Found $toonname in this line:>>>$_<<<\n";
	}
	return 1;
}

#######################################################################
# collect gear listings
sub parse_gear_list_header {
	# From uses of !list contents on a container

	# Loot lines and rarity - skip "Common" and "Uncommon" stuff
	if (/(.+): (Non-random|Beyond Ultrarare|Ultrarare|Rare) items:/) {
		# TODO: if ($toon eq $q) ...
	    $gearcontainer = $1;
		#if ($parse_sub_mode ne 'gear') {
	print "reset gearcontainer $gearcontainer\n" if (exists($Gear{$gearcontainer}) && !$next_item_rarity);
			# Now clear the existing data if that exists
			$Gear{$gearcontainer} = () if (exists($Gear{$gearcontainer}) && !$next_item_rarity);
			$parse_sub_mode = 'gear';
		#}
		$next_item_rarity = $2; # TODO: use that data
	}
	elsif (/\[Server\] Contents of Persistent (Transfer|Storage) Chest:/) {
	    $gearcontainer = "Bankchest $bankchest";
		$parse_sub_mode = 'gear';
	    # Now clear the existing data if that exists
	    $Gear{$gearcontainer} = () if (exists($Gear{$gearcontainer}));
		$next_item_rarity = ''; # unknown rarity
	}
	elsif (/You are now using bank chest '(.+?)'/) {
	    $bankchest = $1;
	}
	elsif (/You are now using your default bank chest/) {
	    $bankchest = "default";
	}
	else {
		return 0;
	}

	return 1;
}

# collect gear data from "!list inventory" or "!list contents"
sub parse_sm_gear {
	if (/^    ([A-Za-z].+)/) {
	    if ($gearcontainer ne "") {
			$Gear{$gearcontainer}{$1}++;
	    }
		# TODO: if ($next_item_rarity) ...
	    return 1;
	}
}

sub parse_sm_end_gear {
	return if ($next_item_rarity && /^\s*$/); # items of other rarity may follow
	$parse_sub_mode = '';
}

#######################################################################
# area specific stuff - for now only hells
#

# Specific hell comments
# Not sure what to use those for atm
sub parse_line_area_Hells {
	if (/^(Asmodeus stuns you with Malbolge's Strike|The malebranche's wing buffet knocks you to the ground|Asmodeus smites you with Maladomini's Ruin|Asmodeus infects you with Avernan Ague|The brood worm siphons some of your magical energies, and strikes you mute with awe|The erinyes has entangled you|The malebranche performs a whirl, catching you on its blade|The malebranche snatches you up and drops you, but you glide back to the ground|The pit fiend's wing buffet knocks you down|The pit fiend calls down a meteor swarm)!$/) {
		$saves -> insert('end',$_, 'yellow');
		return 1;
	}
	if (/The Amnizu has stricken you with amnesia!/) {
	    $saves -> insert('end',$_, 'yellow');
		# TODO: remember amni until rest
	    return 1;
	}
	if (/^(.+) : Restore Hells Penalties/) {
		#print "GR: by '$1' @ $server_uptime/$server_round\n";
		# TODO: start counting rounds
		return 1;
	}

	return 0;
}

# player commands to control YAL
sub parse_player_cmds {
	if (/\Q$toon\E: \[Whisper\] \.(.+)/) {
		my $command = $1;
		if ($command eq "clear" || $command eq "reset") {
			reset_all();
		}
		elsif ($command eq "pstats") {
			dialog_party_summary();
		}
		elsif ($command eq "who") {
			$catchpartywho = 1;
		}

		return 1;
	}
}

#######################################################################
# Processing functions

#
#
# process attack data
#
sub process_attack {
    my ($attacker, $defender, $attacktype, $roll, $ab, $status) = @_;

    $swings{$attacker}++;
    $swingsagainst{$defender}++;
    $Swings{$attacker}{$defender}++;
    
    # Make sure to update the AB and AC estimate
    $AB{$attacker} = 0 if (!exists($AB{$attacker}));
    $AB{$attacker} = $ab if ($ab > $AB{$attacker});
    
    if ($status eq "hit" || $status eq "crit") {
	$hits{$attacker}++;
	$Hits{$attacker}{$defender}++;

	if ($status eq "crit") {
	    $crits{$attacker}++;
	    $Crits{$attacker}{$defender}++;		    
	}
	
	$hits++ if ($attacker eq $toon);
	if ($roll<20) {
	    if ((!exists($MinAC{$defender})) || ($ab+$roll < $MinAC{$defender})) {
		$MinAC{$defender} = $ab+$roll;
	    }
	}

	# special attacks
	# TODO: this can't be all ...
	$Disarm{$attacker}{$defender}++ if ($attacktype eq "Improved disarm");

    }
    elsif ($status eq "miss" && $roll>1) {
	$dodge{$defender}++;
	$MaxAC{$defender} = 0 if (!exists($MaxAC{$defender}));
	$MaxAC{$defender} = $ab+$roll if ($ab+$roll > $MaxAC{$defender});
    }
    elsif ($status =~ /(\d+)\%/) {
	$dodge{$defender}++;
	$conceal{$defender} = $1 if (!exists($conceal{$defender}));
	$conceal{$defender} = $1 if $1 > $conceal{$defender};
	$Conceals{$attacker}{$defender}++;
	$status = "c$1%"; # for better display?
    }
    else {
	$dodge{$defender}++;
    }

    $hits{$attacker} = 0 if (!exists($hits{$attacker}));
    $hitpercentage{$attacker} = sprintf("%3.2f %%", $hits{$attacker}/$swings{$attacker}*100);
    
    if ($OPTIONS{"badboy"}==1) {
	$badtooncounter{$attacker}++ if (hg_do_not_hit($defender));
    }
    
    if ($toon eq $attacker) {
	$hitfrequency = ($hitfrequencyweight*$hitfrequency)/($hitfrequencyweight + 1);
	if ($status eq "hit" || $status eq "crit" ) {
	    $hitfrequency += 1/($hitfrequencyweight + 1);
	}
	append_attack($hits_out, $ab, $roll, $status, $hitfrequency*100, $defender, 'green');
    }
    elsif ($toon eq $defender) {
	$defencefrequency = ($hitfrequencyweight*$defencefrequency)/($hitfrequencyweight + 1);
	if ($status ne "hit" && $status ne "crit" ) {
	    $defencefrequency += 1/($hitfrequencyweight + 1);
	}
	append_attack($hits_inc, $ab, $roll, $status, $defencefrequency*100, $attacker, 'red');
    }
}

sub start_timer {
    my $array = $_[0];
    push(@$array, $_[1]);
}


# This function is supposed to replace start_timer when all timers get implemented as hashes
sub starttimer {
    my $array = $_[0];
    push(@$array, $_[1]);
}
#ills effect
sub update_effects_timers{
	
	#required line for gui
	$othertimers->delete("1.0", 'end');
	
	#Create ordered listing of effect times sorted by time
	my @sortedEffects = sort {$Effecttimers{$a} <=> $Effecttimers{$b}} keys %Effecttimers;
	foreach my $EffectName (@sortedEffects){
		#print "$EffectName $Effecttimers{$EffectName}\n";
		#decrement the value on each hash
		#delete timer if it is 0
		
		$Effecttimers{$EffectName} = $Effecttimers{$EffectName} - 1;
		if ($Effecttimers{$EffectName} eq 0){delete $Effecttimers{$EffectName};}
		
		
			
		#format the effect to to window
		my $etimertext = sprintf "%2d:%02d %s \n", integer_div($Effecttimers{$EffectName}, 60), ($Effecttimers{$EffectName} % 60), $EffectName;
		#place the effect in the window
		$othertimers -> insert('end', $etimertext);
		
	}
	@sortedEffects = {};
	
	
	#beyond this line is the old way
    #if (exists($etimers{0})) {
	#delete($etimers{0});
    #}
    #foreach my $etime (sort {$a <=> $b} keys(%etimers)) {
	#if ($debug){print "$etime";}
	#$etimers{$etime-1} =[@{$etimers{$etime}}];

	#foreach my $effecttimer (@{$etimers{$etime}}) {
		#if ($debug){print "$effecttimer \n";}
	    #my $etimertext = sprintf "%2d:%02d %s \n", integer_div($etime, 60), ($etime % 60), $effecttimer;

		#$othertimers -> insert('end', $etimertext);

	#}
	#end the old way
	#delete($etimers{$etime});
    #}
	#end the old way
}

sub update_death_timers {
    $fuguetimers->delete("1.0", 'end');
	#$othertimers->delete("1.0", 'end');
	
    if (exists($timers{0})) {
	delete($timers{0});
    }
    foreach my $time (sort {$a <=> $b} keys(%timers)) {	
	$timers{$time-1} =[@{$timers{$time}}];
	if ($time<11 && $OPTIONS{"fuguebeep"}) {
	    $mw -> bell;
	}
	foreach my $player (@{$timers{$time}}) {
	    my $timertext = sprintf "%2d:%02d %s \n", integer_div($time, 60), ($time % 60), $player;
	    my $s = ($player eq $toon) ? 'self' : '';
	    if ($time<10) {
		$fuguetimers -> insert('end', $timertext, "critical$s") ;
	    }
	    elsif ($time<30) {
		$fuguetimers -> insert('end', $timertext, "critical$s") ;
	    }
	    elsif ($time<60) {
		$fuguetimers -> insert('end', $timertext, "warning$s"); 
	    }
	    else {
		$fuguetimers -> insert('end', $timertext, $s);
	    }
	}
	delete($timers{$time});
    }
# taken out into effects sectoin
#    $othertimers = "";
#    if (@grtimer) {
#	shift(@grtimer) if ($grtimer[0]<1);
#	if (@grtimer) {
#	  #  $grtimer[0]--;
	 #   $othertimers .= sprintf "GSanc %2d:%02d", integer_div($grtimer[0], 60), ($grtimer[0] % 60);
#	}
 #   }
#    if (@gstimer) {
#	shift(@gstimer) if ($gstimer[0]<1);
#	if (@gstimer) { 
#	  #  $gstimer[0]--;
	  #  $othertimers .= "\n" if (@grtimer);
	  #  $othertimers .= sprintf "GSmit %2d:%02d", integer_div($gstimer[0], 60), ($gstimer[0] % 60);
#	}
 #   }
}


sub clear_last_fugue_timer() {
#    pop(@{$timers{300}});        
}


sub integer_div {
  my ($a, $b) = @_;
  return(($a - ($a % $b)) / $b);
}

sub min {
  my ($a, $b) = @_;

  if ($a < $b) {
      return $a;
  }
  else {
      return $b;
  }
}

sub max {
  my ($a, $b) = @_;

  if ($a > $b) {
      return $a;
  }
  else {
      return $b;
  }
}

sub inc_logcount {
    $logfilenumber++; 
    $logfilenumber = 1 if ($logfilenumber>4);

    $currentlogfile = "nwclientLog". $logfilenumber .".txt";

    close(LOGFILE);
    open(LOGFILE, "$currentlogfile");
}

sub print_immunities {
    $imms -> delete("1.0", 'end');
    # Remove physical
    foreach (@DAMAGETYPESIMM) {
	my $t = $immunities{$_};
	# TODO: make option if to show resists
	$t .= '|' . $resists{$_} if ($resists{$_});
	#$imms -> insert('end',  $immunities{$_}. "\t", "$COLOURS{$_}");
	$imms -> insert('end',  $t. "\t", "$COLOURS{$_}");  
    }
}


#
# Check if we should update the current log file
#
sub check_log_file {
    # Find the next logfile name
    my $nextlogfile = "nwclientLog". ($logfilenumber+1) .".txt";
    if ($logfilenumber>3) {
	$nextlogfile = "nwclientLog1.txt";	
    }

    # Check if the next file exists and if it has a newer timestamp than the current file
    if (-e $nextlogfile) {	
	inc_logcount() if ((-M $nextlogfile) <= (-M $currentlogfile));
    }
}


#
# This hasn't been updated in some time. Probably not resetting everything correctly but then I never use it anyway
#
sub reset_all {
    $deaths = 0;
    $kills = 0;
    $totalxp = 0;
    $lastkilled="";
    $lastkiller="";

    @grtimer = ();
    @gstimer = ();
    $timertext = "";
    $other = "";

    $hitfrequency = 0;
    $defencefrequency = 0;


    %kills = ();
    %deaths = ();
    %swings = ();
    %damage_done = ();
    %partykiller = ();
    %partykilled = ();
    %badtooncounter = (); 
    %partyhits = ();
    %partyattacks = ();


    %Kills = ();

    %listofplayers=();
    %hitpercentage = ();
    

    $damage_inc->delete("1.0", 'end');
    $damage_out->delete("1.0", 'end');
    $hits_inc->delete("1.0", 'end');
    $hits_out->delete("1.0", 'end');   
    $saves->delete("1.0", 'end');
    $resists->delete("1.0", 'end');   
}


sub clear_party {
    %party = ();
    $party{$toon} = 1;    
}

#
# This starts the dialog window where you can enter party members
#
sub dialog_party_entry {
    my $party_dialog;
	if ($debug){print "old $party_dialog \n";}
    # Should really clear the old party list
    if (!Exists($party_dialog)) {
		my %pty = ();
		# Get the names of the people in the current party
		my @existingparty = keys(%party);
		if ($debug) {print "@existingparty \n";
	}
	$party_dialog = $mw->Toplevel();
#	$party_dialog->attributes(-topmost=>1);
	$party_dialog->title("Party member setup");

	$party_dialog->LabEntry(-textvariable => \$toon,
				-label => "Own character",
				-labelPack => [qw/-side left -anchor w/]) -> pack();

	for (my $i=2; $i<=10; $i++) {
	    # Fill up the choises with existing party members	    
	    if (@existingparty) {
		$_ = shift(@existingparty);
		$_ = shift(@existingparty) if ($_ eq $toon);
		$pty{$i} = $_;
	    }

	    my $thistoon = $party_dialog->BrowseEntry(-variable => \$pty{$i},
				       -label => "Member $i");

	    foreach $_ (sort { $listofplayers{$b} <=> $listofplayers{$a} || $a cmp $b } keys %listofplayers) {
		$thistoon->insert("end", $_);
	    }	    
	    $thistoon-> pack(-anchor=>'e');

	}
	$party_dialog->Button(-text => "Ok",
			      -command => sub { $party_dialog->withdraw();
						$party_dialog->grabRelease();
						clear_party();
						new_party_member($toon);
						for (my $i=2; $i<=10; $i++) {
						    if (defined($pty{$i})) {
							if ($pty{$i} ne "" && !exists($party{$pty{$i}})) {
							    new_party_member($pty{$i});
							}
						    }
						}
						undef($party_dialog);
					    }) -> pack();


	$party_dialog->raise();
	$party_dialog->grab();
    }
    else {
	$party_dialog->deiconify();
	$party_dialog->raise();

    }
}


#
# This function generates the party summary window and displays the necessary information
#
sub dialog_party_summary {
    my $party_summary;
    
    # We only want one copy of this window
    if (!Exists($party_summary)) {
		my %pty = ();

		$party_summary = $mw->Toplevel();
		$party_summary->title("Party summary statistics");

		my $ps_frm = $party_summary->Frame()->pack(-side=>'top');
		my $col = 0;
		my $row = 0;
		for my $hname ('Toon', 'Kills', 'Last Killed', 'Deaths', 'Last Killer', 'Damage', 'Hit%', 'Holla') {
			$ps_frm->Label(-text => $hname, -relief => 'ridge')->grid(-row => $row, -column => $col++, -sticky => 'we');
		}

		# Place OK button at bottom
		$party_summary->Button(-text => "Ok", -command => sub {
			$party_summary->withdraw();						 
		}) -> pack(-side=>'bottom');

		# Now generate a row frame for each party member to display the information
		# TODO: If the verticalsummary is 1 then make it as columns instead - lost with new party dialog
		my %frm_party = ();
		my $pfont = [-weight => 'normal', -family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}];
		foreach my $id (sort (keys(%party))) {	    

			# TODO: check if it's an active partymember or was just logged on in between
			$col = 0;
			$row++;

			$hitpercentage{$id} = 0 if (!defined($hitpercentage{$id}));
			$badtooncounter{$id} = 0 if (!defined($badtooncounter{$id}));

			$ps_frm->Label(-text => $id, -relief => 'ridge')
				->grid(-row => $row, -column => $col++, -sticky => 'nswe');
			$ps_frm->Label(-textvariable => \$kills{$id}, -relief => 'ridge', -font => $pfont)
				->grid(-row => $row, -column => $col++, -sticky => 'nswe');
			$ps_frm->Label(-textvariable => \$partykilled{$id}, -relief => 'ridge', -font => $pfont)
				->grid(-row => $row, -column => $col++, -sticky => 'nswe');
			$ps_frm->Label(-textvariable => \$deaths{$id}, -relief => 'ridge', -font => $pfont)
				->grid(-row => $row, -column => $col++, -sticky => 'nswe');
			$ps_frm->Label(-textvariable => \$partykiller{$id}, -relief => 'ridge', -font => $pfont)
				->grid(-row => $row, -column => $col++, -sticky => 'nswe');
			$ps_frm->Label(-textvariable => \$damage_done{$id}, -relief => 'ridge', -font => $pfont)
				->grid(-row => $row, -column => $col++, -sticky => 'nswe');
			$ps_frm->Label(-textvariable => \$hitpercentage{$id}, -relief => 'ridge', -font => $pfont)
				->grid(-row => $row, -column => $col++, -sticky => 'nswe');
			$ps_frm->Label(-textvariable => \$badtooncounter{$id}, -relief => 'ridge', -font => $pfont)
				->grid(-row => $row, -column => $col++, -sticky => 'nswe');
		}
    }
    else {
		$party_summary->deiconify();
		$party_summary->raise();	
    }
}

sub dialog_program_options {
    my $options_dialog;   
    
    # We only want one copy of this window
    if (!Exists($options_dialog)) {
	$options_dialog = $mw -> Toplevel();
	$options_dialog->title("Options");
	
	# Place OK button at bottom
	$options_dialog->Button(-text => "Ok",
				-command => sub { $options_dialog->withdraw();
						  save_configuration();
						  configure_fonts();
					      }) -> pack(-side=>'bottom');

	my $fontsetup = $options_dialog -> Frame(-label =>"Fonts", -relief=>'ridge', -borderwidth=>2)  -> pack(-side=>'top', -fill=>'x');       

        # Fonts
	my $fontcfg_dmg = $fontsetup -> Frame() -> pack(-side=>'top', -fill=>'x');
        my $fontlist = $fontcfg_dmg->BrowseEntry(-label => "Damage windows", -variable=>\$OPTIONS{"font"}, -labelPack=>[-side=>'top'])->pack(-side=>'left');
	$fontlist->insert('end', sort $mw->fontFamilies);
#	$fontsetup->Label(-text=>"Font size:")->pack();
	$fontcfg_dmg->Scale( -orient=>'horizontal', -width=>20, -from=>5, -to=>16,
				-showvalue=>1, -variable=>\$OPTIONS{"fontsize"} )->pack(-side=>'left', -anchor=>'s');

	my $fontcfg_hits = $fontsetup -> Frame() -> pack(-side=>'top', -fill=>'x');
        my $fontlisthit = $fontcfg_hits->BrowseEntry(-label => "Hit windows", -variable=>\$OPTIONS{"font-hit"}, -labelPack=>[-side=>'top']) -> pack(-side=>'left');
	$fontlisthit->insert('end', sort $mw->fontFamilies);
	$fontcfg_hits->Scale( -orient=>'horizontal', -width=>20, -from=>5, -to=>16,
				-showvalue=>1, -variable=>\$OPTIONS{"fontsize-hit"} )->pack(-side=>'left', -anchor=>'s');


	my $fontcfg_resist = $fontsetup -> Frame()  -> pack(-side=>'top', -fill=>'x');
        my $fontlistresist = $fontcfg_resist->BrowseEntry(-label => "Resist/saves windows", -variable=>\$OPTIONS{"font-resist"}, -labelPack=>[-side=>'top']) -> pack(-side=>'left');
	$fontlistresist->insert('end', sort $mw->fontFamilies);
	$fontcfg_resist->Scale( -orient=>'horizontal', -width=>20, -from=>5, -to=>16,
				-showvalue=>1, -variable=>\$OPTIONS{"fontsize-resist"} )->pack(-side=>'left', -anchor=>'s');

	my $viewsetup = $options_dialog -> Frame(-label =>"View", -relief=>'ridge', -borderwidth=>2)  -> pack(-side=>'top', -fill=>'x');
	$viewsetup->Checkbutton(-text => "Display hit counter", 
				     -variable => \$OPTIONS{"hitcounter"},
				     -command => sub { 
					 if ($OPTIONS{"hitcounter"} == 1) {
					     $frm_dynamicwindow -> pack(-side=>'bottom', -fill=>'x');
					 } else {
					     $frm_dynamicwindow -> pack('forget');					     
					 }
				     }) -> pack(-anchor=>"w");
	
	$viewsetup->Checkbutton(-text => "Force autoscroll", 
				     -variable => \$OPTIONS{"fixscroll"}
				     ) -> pack(-anchor=>"w");


	$viewsetup->Checkbutton(-text => "Horizontal party summary", 
				     -variable => \$OPTIONS{"verticalsummary"}
				     ) -> pack(-anchor=>"w");

	$viewsetup->Checkbutton(-text => "Show spells cast by you", 
				     -variable => \$OPTIONS{"ownspells"}
				     ) -> pack(-anchor=>"w");

	$viewsetup->Checkbutton(-text => "Show spells cast by others", 
				     -variable => \$OPTIONS{"otherspells"}
				     ) -> pack(-anchor=>"w");

	$viewsetup->Checkbutton(-text => "Skip unknown spells", 
				     -variable => \$OPTIONS{"skipunknownspells"}
				     ) -> pack(-anchor=>"w");

	my $combat_info_frm = $options_dialog -> Frame(-label =>"Combat Info", -relief=>'ridge', -borderwidth=>2)  -> pack(-side=>'top', -fill=>'x');
	$combat_info_frm->Checkbutton(-text => "Show monster race", 
				     -variable => \$OPTIONS{"showmonsterrace"}
				     ) -> pack(-anchor=>"w");

	$combat_info_frm->Checkbutton(-text => "Show monster flags", 
				     -variable => \$OPTIONS{"showmonsterflags"}
				     ) -> pack(-anchor=>"w");

	$combat_info_frm->Checkbutton(-text => "Show monster healing info", 
				     -variable => \$OPTIONS{"showmonsterheal"}
				     ) -> pack(-anchor=>"w");

	$combat_info_frm->BrowseEntry(-width=>4,
				     -label => "Show esoteric damage", 
				     -variable => \$OPTIONS{"showesotericdmg"},
				     -choices => ['no', 'sum', 'full']
				     ) -> pack(-anchor=>"w");

	$options_dialog->Checkbutton(-text => "Capture toon name from scry and login", 
				     -variable => \$OPTIONS{"catchtoonname"}
				     ) -> pack(-anchor=>"w");

	$options_dialog->Checkbutton(-text => "Show paragon percentage", 
				     -variable => \$OPTIONS{"showparagons"}
				     ) -> pack(-anchor=>"w");

	$options_dialog->Checkbutton(-text => "Show 'clear stats' messagebox when entering hell", 
				     -variable => \$OPTIONS{"hellentrymessagebox"}
				     ) -> pack(-anchor=>"w");
	
	my $beepthing = $options_dialog->Checkbutton(-text => "Beep on fugue", 
				     -variable => \$OPTIONS{"fuguebeep"},
				     -state=>'disabled'
				     ) -> pack(-anchor=>"w");


#	my $balloon = $options_dialog->Balloon(-state=>'balloon');
#	$balloon->attach($beepthing, -balloonmsg => "Start beeping on fugue");
	#
	# Blame'O'Meter score
	#
#	my $hollasetup = $options_dialog -> Frame(-label =>"Blame'O'Meter", -relief=>'ridge', -borderwidth=>2)  -> pack(-side=>'top', -fill=>'x');
#	$hollasetup->Checkbutton(-text=>'Record Holla score', -variable=>\$OPTIONS{"badboy"})->pack();

	$options_dialog->Checkbutton(-text => "Automatically start a run", 
				     -variable => \$OPTIONS{"autostartrun"}
				     ) -> pack(-anchor=>"w");
	
    }
    else {
	$options_dialog->deiconify();
	$options_dialog->raise();	
    }
}



sub dialog_detailed_summary {
    my $details_dialog;   
    
    # We only want one copy of this window
    if (!Exists($details_dialog)) {
	$details_dialog = $mw -> Toplevel();
	$details_dialog->title("Detailed summary");


	$details_dialog->ItemStyle(
				   'text',
				   -stylename => 'party',
				   -fg        => 'black',
				   -bg        => 'lightblue',
				   );
	

	
	# Place OK button at bottom
	$details_dialog->Button(-text => "Ok",
				-command => sub { $details_dialog->destroy();
					      }) -> pack(-side=>'bottom');

	my @headers = ("Name", "AB", "AC range", "Conceal", "Max SR", "Kills", "Deaths", "Immunities", "Deals", "Takes");

	my $grid = $details_dialog->Scrolled('HList',
					     -head       => 1,
					     -columns    => scalar @headers,
					     -scrollbars => 'e',
					     -width      => 40,
					     -height     => 10,
					     -background => 'white',
					     )->pack(-fill=>"both", -expand=>1);

	foreach my $i ( 0 .. $#headers ) {
	    $grid->header('create', $i,
			  -text             => $headers[$i],
			  -headerbackground => 'gray',
			  );
	}

	# Update vulnerabilities
	calculate_vulnerabilities();


	# Find the list of critters we want to show info on 
	my %critterlist;
	@critterlist{(keys(%party), keys(%kills), keys(%deaths))} = ();
	foreach $_ (sort keys %critterlist) {
	    $grid->add($_);
	    if (exists($party{$_})) {
		$grid->itemCreate($_, 0, -text => $_, -style=>"party");
	    }
	    else {
		$grid->itemCreate($_, 0, -text => $_);
	    }
	    if (exists($AB{$_})) {
		$grid->itemCreate($_, 1, -text => $AB{$_});
	    }
	    else {
		$grid->itemCreate($_, 1, -text => "");
	    }
	    $MinAC{$_} = "" if (!exists($MinAC{$_}));
	    $MaxAC{$_} = "" if (!exists($MaxAC{$_}));
	    $grid->itemCreate($_, 2, -text => ($MinAC{$_} . " - " . $MaxAC{$_}));

	    if (exists($conceal{$_})) {
		$grid->itemCreate($_, 3, -text => $conceal{$_});
	    }
	    else {
		$grid->itemCreate($_, 3, -text => "");
	    }


	    if (exists($SR{$_})) {
		$grid->itemCreate($_, 4, -text => $SR{$_});
	    }
	    else {
		$grid->itemCreate($_, 4, -text => "");
	    }
	    
	    $grid->itemCreate($_, 5, -text => $kills{$_});
	    $grid->itemCreate($_, 6, -text => $deaths{$_});

	    # Immunities
	    my $imm = "";
	    $imm .= "Cr " if (exists($immune{$_}{"Critical Hits"}));
	    $imm .= "Sn " if (exists($immune{$_}{"Sneak Attacks"}));
	    $imm .= "Mi " if (exists($immune{$_}{"Mind Affecting Spells"}));
	    $imm .= "B7 " if (exists($immune{$_}{"Bigby's Grasping Hand"}));
	    $imm .= "Im " if (exists($immune{$_}{"Implosion"}));
	    $imm .= "DM " if (exists($immune{$_}{"Death Magic"}));
	    $grid->itemCreate($_, 7, -text => $imm);


	    $grid->itemCreate($_, 9, -text => $damage_takenstr{$_});
	}

    }
    else {
	$details_dialog->deiconify();
	$details_dialog->raise();	
    }
}


sub dialog_chat_log {
    # We only want one copy of this window
    if (!Exists($chatlog_dialog)) {
	$chatlog_dialog = $mw -> Toplevel();
	$chatlog_dialog->withdraw();
	$chatlog_dialog->title("Chat summary");
	$chatlog_dialog->protocol('WM_DELETE_WINDOW' => sub { $chatlog_dialog->withdraw() });  # Capture the destroy icon

	
	$chatlog_dialog->Button(-text => "Ok",
				-command => sub { $chatlog_dialog->withdraw();
					      }) -> pack(-side=>'bottom');
	
	$chatlog = $chatlog_dialog -> Scrolled('Text', -width=>60, -height=>4, 
					       -foreground=>'white', -background=>'black',
					       -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}],
					       -scrollbars=>'e', -wrap=>'word') -> pack(-side=>'top', -fill=>'both', -expand=>1);       	
    }
    else {
	$chatlog_dialog->deiconify();
	$chatlog_dialog->raise();	
    }
}


sub dialog_effects {
    my $effectsdialog;

    # We only want one copy of this window
    if (!Exists($effectsdialog)) {
	$effectsdialog = $mw -> Toplevel();
	$effectsdialog->title("Summary of effects");

	my $whichtoon;
	my $showeffects;

        my $toonchooser = $effectsdialog->BrowseEntry(-label => "Toons:", -variable=>\$whichtoon, 
						      -browsecmd=> sub {
							  if (exists($Effects{$whichtoon})) {
							      $showeffects->delete("1.0", 'end');
							      foreach my $effect (sort keys(%{$Effects{$whichtoon}})) {
								  
								  $showeffects->insert('end', $effect . "\t" . $Effects{$whichtoon}.  "\n");
							      }
							  }
						      }, 
						      -state=> 'readonly',
						      -labelPack=>[-side=>'top'])->pack(-side=>'top');
	$toonchooser->insert('end', sort keys(%Effects));


	$effectsdialog->Button(-text => "Snapshot",
				-command => sub { $effectsdialog->withdraw();
					      }) -> pack(-side=>'bottom');

	$effectsdialog->Button(-text => "Ok",
				-command => sub { $effectsdialog->withdraw();
					      }) -> pack(-side=>'bottom');
	
	$showeffects = $effectsdialog -> Scrolled('Text', -width=>60, -height=>4, 
						  -foreground=>'white', -background=>'black',
						  -tabs => [qw/.3i/],
						  -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}],
						  -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'top', -fill=>'both', -expand=>1);


        Win32::API->new("user32","SetWindowPos",[qw(N N N N N N N)],'N')->Call(hex($effectsdialog->frame()),-1,0,0,0,0,3);



	# Win32::API->new("user32","SetWindowPos",[qw(N N N N N N N)],'N')->Call(hex($tl->frame()),-2,0,0,0,0,3);


	
    }
    else {
	$effectsdialog->deiconify();
	$effectsdialog->raise();	
    }
}


sub html_summary {
    my $file = $mw->getSaveFile(-initialfile=> 'lastrun.html',
				-filetypes=>[['HTML files', '.html'],
					     ['All Files', '*']],
				-defaultextension => '.html');

    if (defined($file)) {
	calculate_vulnerabilities();
	open(SAVEFILE, ">$file");

	print SAVEFILE "<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01//EN\">\n";
	print SAVEFILE "<html><head><title>NWN run summary</title>";
	# All style options are set here so keep the info in one document instead of distributiong a CSS file as well
	print SAVEFILE "<style type=\"text/css\">\n";
	print SAVEFILE "body { font-size: 90% ; margin-left: 2% ; margin-right: 2% ; font-family: Verdana}\n";
	print SAVEFILE "div.combatant { margin-bottom: 20px ; border: 1px solid black ; padding-top: 10px ; padding-bottom: 1% }\n";
	print SAVEFILE "div.details { color: black ; width: 15em }";
	print SAVEFILE "div.vulnBox { color: black ; background-color: #add8e6  }";
	print SAVEFILE "div.immBox { color: black ; background-color: lightgray  }";
	print SAVEFILE "div.damageArea { margin-left: 20% }";
	print SAVEFILE "</style></head>\n";

	print SAVEFILE "<body bgcolor=\"#ffffff\">";
	print SAVEFILE "<h1>Party members</h1>";

	print SAVEFILE "<ul>";
	foreach my $id (sort (keys(%party))) {
	    print SAVEFILE "<li> <a href=\"#$id\">$id</a>";
	}
	print SAVEFILE "</ul>";
	
	print SAVEFILE "<hr>";
	print SAVEFILE "<h1>Party summary</h1>";
	print SAVEFILE "<table border=1>";
	print SAVEFILE "<tr><th bgcolor=lightgray>Name</th><th bgcolor=lightgray>Kills</th><th bgcolor=lightgray>Deaths</th><th bgcolor=lightgray>Damage taken</th><th bgcolor=lightgray>Damage done</th>";
	print SAVEFILE "<th bgcolor=lightgray title=\"Overall hit percentage and 95% confidence interval\">Hit \%</th><th bgcolor=lightgray title=\"Overall dodge percentage and 95% confidence interval\">Dodge \%</th><th bgcolor=lightgray title=\"Number of swings against hell monsters with nasty party kb\">Holla score</th></tr>";
	foreach my $id (sort (keys(%party))) {	    
	    print SAVEFILE "<tr><td>$id</td>";
	    print SAVEFILE "<td align=right>$kills{$id}</td>";
	    print SAVEFILE "<td align=right>$deaths{$id}</td>";
	    print SAVEFILE "<td align=right>$damage_taken{$id}</td>";
	    print SAVEFILE "<td align=right>$damage_done{$id}</td>";
	    if (exists($hitpercentage{$id})) {
		my $ptilde = ($hits{$id}+2) / ($swings{$id}+4);
		my $se = sqrt($ptilde*(1-$ptilde)/($swings{$id}+4));
		print SAVEFILE "<td align=left>$hitpercentage{$id} (" . int(($ptilde-1.96*$se)*1000)/10 . " - " . int(($ptilde+1.96*$se)*1000)/10 .")</td>";
	    }
	    else {
		print SAVEFILE "<td align=center>-</td>";
	    }
	    if (exists($dodge{$id}) & exists($swingsagainst{$id})) {
		my $dodgechance = 100*($dodge{$id} / $swingsagainst{$id});
		my $ptilde = ($dodge{$id}+2) / ($swingsagainst{$id}+4);
		my $se = sqrt($ptilde*(1-$ptilde)/($swingsagainst{$id}+4));
		printf SAVEFILE "<td align=left>%5.2f (%5.2f - %5.2f)</td>", $dodgechance, int(($ptilde-1.96*$se)*1000)/10, int(($ptilde+1.96*$se)*1000)/10;
	    }
	    else {
		print SAVEFILE "<td align=center>-</td>";
	    }
	    print SAVEFILE "<td align=right>" . (exists($badtooncounter{$id}) ? $badtooncounter{$id} : " -") . "</td></tr>";
	}
	print SAVEFILE "</table>";
	
	if ($totalmobkills>0) { 
	    my $numberofparagons = (exists($paracount{1}) ? $paracount{1} : 0) + (exists($paracount{2}) ? $paracount{2} : 0) + (exists($paracount{3}) ? $paracount{3} : 0);
	    print SAVEFILE "<p title=\"Percentage of killed monsters that were paragons\">Paragon percentage: " . int($numberofparagons/$totalmobkills *1000)/10 . "% ";
	    if ($numberofparagons>0) {
		print SAVEFILE "(" . (exists($paracount{1}) ? $paracount{1} : 0);
		print SAVEFILE "/" . (exists($paracount{2}) ? $paracount{2} : 0) . "/";
		print SAVEFILE (exists($paracount{3}) ? $paracount{3} : 0) . ")";		
	    }
	}

	print SAVEFILE "<hr>";
	print SAVEFILE "<h1>Detailed report</h1>\n";
	my %critterlist;
	@critterlist{(keys(%party), keys(%kills), keys(%deaths))} = ();
	foreach $_ (sort keys %critterlist) {
	    print SAVEFILE "<div class=\"combatant\"><h3><a name=\"$_\">$_</a></h3>\n";
	    print SAVEFILE "<table width=100%>";
	    printf SAVEFILE "<tr valign=top><td width=15%% valign=top>Max AB: %3d<br>", exists($AB{$_}) ? $AB{$_} : 0;
	    print SAVEFILE "Max AC: > " . (exists($MaxAC{$_}) ? $MaxAC{$_}+1 : "")  . "<br>";
	    if (exists($SR{$_})) {
		print SAVEFILE "Max SR: $SR{$_}<br>";
	    }
	    else {
		print SAVEFILE "Max SR: -<br>";
	    }
	    if (exists($TR{$_})) {
		print SAVEFILE "Max TR: $TR{$_}<br>";
	    }
	    printf SAVEFILE "Max conceal: %4.0f<br>", (exists($conceal{$_}) ? $conceal{$_} : 0);
	    $kills{$_} = 0 if (!exists($kills{$_}));
	    print SAVEFILE "Kills: $kills{$_}<br>";
	    printf SAVEFILE "Deaths: %4d<br>", (exists($deaths{$_}) ? $deaths{$_} : 0);

	    printf SAVEFILE "<p><p>";
	    printf SAVEFILE "Swings/hits/crits dealt:<br> %4.0f/%4.0f/%4.0f<br>", (exists($swings{$_}) ? $swings{$_} : 0), (exists($hits{$_}) ? $hits{$_} : 0), (exists($crits{$_}) ? $crits{$_} : 0);

	    print SAVEFILE "<p><div class=\"vulnBox\"><b>Max saves:</b><br>";
	    if (exists($Saves{$_})) {
		my $maxsave = 0;
		foreach my $savetype (keys(%{$Saves{$_}{"Fortitude"}{"max"}})) {
		    $maxsave = max($Saves{$_}{"Fortitude"}{"max"}{$savetype}, $maxsave);
		}
		print SAVEFILE "F: " . ($maxsave>0 ? $maxsave : "-") .", ";
		$maxsave=0;
		foreach my $savetype (keys(%{$Saves{$_}{"Reflex"}{"max"}})) {
		    $maxsave = max($Saves{$_}{"Reflex"}{"max"}{$savetype}, $maxsave);
		}
		print SAVEFILE "R: " . ($maxsave>0 ? $maxsave : "-") .", ";
		$maxsave=0;
		foreach my $savetype (keys(%{$Saves{$_}{"Will"}{"max"}})) {
		    $maxsave = max($Saves{$_}{"Will"}{"max"}{$savetype}, $maxsave);
		}	      
		print SAVEFILE "W: " . ($maxsave>0 ? $maxsave : "-") ."<br></div>";
	    }
	    else {
		print SAVEFILE "-<br></div>";
	    }

	    print SAVEFILE "<p><div class=\"immBox\"><b>Immunities:</b><font size=-2><br>", (exists($immune{$_}) ? join(", ", sort (keys(%{$immune{$_}}))) : "-") . "</font></div>";
	    printf SAVEFILE "<p><div class=\"vulnBox\" title=\"The box lists the most common damage types that were taken\"><b>Damage taken:</b><br>%s<br></div>", exists($damage_takenstr{$_}) ? join("<br>",split(/, /, $damage_takenstr{$_})) : "";

	    printf SAVEFILE "<p><div class=\"vulnBox\" title=\"The box lists the elements/exotics that this mob might be immune to. Note this is influenced by non-resistable damage\"><b>Damage immunity:</b><br>%s<br></div>", (exists($elemental_immunities{$_}) ? join("<br>",sort(keys(%{$elemental_immunities{$_}}))) : "");
	    
	    printf SAVEFILE "<p><div class=\"vulnBox\" title=\"Guesstimate of damage types done when you are hit by this PC/monster\"><b>Damage types dealt:</b><br>%s<br></div>", exists($DamageTypesDealt{$_}) ? join("<br>", keys %{ $DamageTypesDealt{$_}} ) : "No clue";

	    if (exists($AbilityChecks{$_})) {
		print SAVEFILE  "<p title=\"Notice these can be influenced by gear\"><b>Ability Checks:</b><br>";
		foreach my $abcheck (keys(%{$AbilityChecks{$_}})) {
		    print SAVEFILE substr($abcheck, 0, 3). ": " . $AbilityChecks{$_}{$abcheck} . "   ";
		}
	    }

	    if (exists($SkillChecks{$_})) {
		print SAVEFILE  "<p title=\"Notice these can be influenced by gear\"><b>Skill Checks:</b><br>";
		foreach my $abcheck (keys(%{$SkillChecks{$_}})) {
		    print SAVEFILE substr($abcheck, 0, 4). ": " . $SkillChecks{$_}{$abcheck} . "   ";
		}
	    }

	    print SAVEFILE "</td><td valign=top>";
	    print SAVEFILE "<b>Damage dealt:</b><p>";
	    print SAVEFILE "<font size=\"-1\">";
	    print SAVEFILE "<table width=100% border=1><tr><th width=40% bgcolor=lightgray>Name</th><th bgcolor=lightgray width=6%>Kills</th><th bgcolor=lightgray width=10%>Swings/hits/crits</th><th bgcolor=lightgray width=25%>Hit %</th><th bgcolor=lightgray>Total damage</th></tr>";
	    my %defenderlist;
	    @defenderlist{(keys(%{$Kills{$_}}), keys(%{$TotalDamage{$_}}), keys(%{$Swings{$_}}))}  = ();
	    foreach my $defender (sort keys %defenderlist) {
		print SAVEFILE "<tr><td>$defender</td>";
		print SAVEFILE "<td align=right>" . (exists($Kills{$_}{$defender}) ? $Kills{$_}{$defender} : "") . "</td>";

		print SAVEFILE "<td width=10%><table border=0><tr>";
		printf SAVEFILE "<td width=8%% align=left>%s</td>", (exists($Swings{$_}{$defender}) ? $Swings{$_}{$defender} : "");
		printf SAVEFILE "<td width=5%% align=center>%s</td>", (exists($Hits{$_}{$defender}) ? $Hits{$_}{$defender} : "");
		printf SAVEFILE "<td width=5%% align=right>%s</td>", (exists($Crits{$_}{$defender}) ? $Crits{$_}{$defender} : "");
		print SAVEFILE "</tr></table></td>";


		print SAVEFILE "<td width=15%><table border=0><tr><td width=5% align=left>";
		
		if (exists($Swings{$_}{$defender}) && $Swings{$_}{$defender}>0) {
		    $Hits{$_}{$defender} = 0 if (!exists($Hits{$_}{$defender}));

		    my $ptilde = ($Hits{$_}{$defender}+2) / ($Swings{$_}{$defender}+4);
		    my $se = sqrt($ptilde*(1-$ptilde)/($Swings{$_}{$defender}+4));
		    print SAVEFILE int(1000*($Hits{$_}{$defender}/$Swings{$_}{$defender}))/10 . "%</td><td align=center width=15%>(" . int(($ptilde-1.96*$se)*1000)/10 . " - " . int(($ptilde+1.96*$se)*1000)/10 .")</td>";
		}
		else {
		    print SAVEFILE "</td><td></td>";		    
		}
		print SAVEFILE "<td align=right width=5%>";
		if (exists($Swings{$_}{$defender}) && $Swings{$_}{$defender}>0) {
		    $Conceals{$_}{$defender} = 0 if (!exists($Conceals{$_}{$defender}));
		    $Hits{$_}{$defender} = 0 if (!exists($Hits{$_}{$defender}));
		    if ($Swings{$_}{$defender} == $Conceals{$_}{$defender}) {
			print SAVEFILE "0"
		    }
		    else {
			print SAVEFILE int(1000*$Hits{$_}{$defender} / ($Swings{$_}{$defender} - $Conceals{$_}{$defender}))/10 . "%";
		    }
		}
		print SAVEFILE "</td>";
		print SAVEFILE "</tr></table>";


		print SAVEFILE "<td align=right>" . (exists($TotalDamage{$_}{$defender}) ? $TotalDamage{$_}{$defender} : "") . "</td></tr>"
		
	    }
	    print SAVEFILE "</table>";
	    print SAVEFILE "</font>";

	    print SAVEFILE "<p><b>Damage received:</b><p>";
	    print SAVEFILE "<font size=\"-1\">";
	    print SAVEFILE "<table width=100% border=1><tr><th width=40% bgcolor=lightgray>Name</th><th bgcolor=lightgray width=6%>Deaths by</th><th bgcolor=lightgray width=10%>Attacks by</th><th bgcolor=lightgray width=25%>Hit %</th><th bgcolor=lightgray>Total damage</th></tr>";	    
            foreach my $id (sort keys %Kills) {
		if ( exists($Kills{$id}{$_}) || exists($TotalDamage{$id}{$_}) || exists($Swings{$id}{$_})) {
		    print SAVEFILE "<tr><td>$id</td><td align=right>" . (exists($Kills{$id}{$_}) ? $Kills{$id}{$_} : "") . "</td>";
		    print SAVEFILE "<td align=right>" . (exists($Swings{$id}{$_}) ? $Swings{$id}{$_} : "") . "</td>";
		    printf SAVEFILE "<td align=right>%5.1f</td>", ((exists($Swings{$id}{$_}) && exists($Hits{$id}{$_})) ? 100*($Hits{$id}{$_}/$Swings{$id}{$_}) : 0);
		    print SAVEFILE "<td align=right>" . (exists($TotalDamage{$id}{$_}) ? $TotalDamage{$id}{$_} : "") . "</td></tr>";
		}
	    }
	    print SAVEFILE "</table>";
	    print SAVEFILE "</font>";
	    print SAVEFILE "</td>";
	    print SAVEFILE "</tr></table></div><p>\n";
	}	
	if ($shamelessadvertising ==1) {
	    print SAVEFILE "Edits by Illandous may have helped you on your run.  Thank him by giving him a bur :P <a href=\"http://highergroundpoa.proboards3.com/index.cgi?board=software&action=display&thread=10946\">NWN-logger</a> v" . $version . " by Claus Ekstroem. Edits by Illandous.</p>\n";
	}
	else {
	    print SAVEFILE "<p>This summary was generated by <a href=\"http://highergroundpoa.proboards3.com/index.cgi?board=software&action=display&thread=10946\">NWN-logger</a> v" . $version . " by Claus Ekstroem. Edits by Illandous.</p>\n";
	}
	print SAVEFILE "</body></html>";
	close(SAVEFILE);
    }    
}


sub save_inventories {
    my $file = $mw->getSaveFile(-initialfile=> 'gear.html',
				-filetypes=>[['HTML files', '.html'],
					     ['ASCII files', '.txt'],
					     ['All Files', '*']],
				-defaultextension => '.html');
    $file =~ /.*\.(.*)/;
    my $extension = $1;

    if (defined($file)) {
	open(SAVEFILE, ">$file");

	if ($extension eq "txt") {
	    foreach my $container (sort keys (%Gear)) {
		print SAVEFILE "Container ($container):\n=====================\n\n";
		foreach my $item (sort keys (%{$Gear{$container}})) {
		    print SAVEFILE "  $item";
		    print SAVEFILE " x$Gear{$container}{$item}" if ($Gear{$container}{$item}>1);
		    print SAVEFILE "\n";
		}
		print SAVEFILE "\n\n";
	    }
	}
	else {
	    print SAVEFILE "<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01//EN\">\n";
	    print SAVEFILE "<html><head><title>NWN inventories</title>";
	    print SAVEFILE "<style type=\"text/css\">\n";
	    print SAVEFILE "body { font-size: 90% ; margin-left: 2% ; margin-right: 2% ; font-family: Verdana}\n";
	    print SAVEFILE "div.combatant { margin-bottom: 20px ; border: 1px solid black ; padding-top: 10px ; padding-bottom: 1% }\n";
	    print SAVEFILE "A:link {text-decoration: none} A:visited {text-decoration: none} A:active {text-decoration: none} A:hover {text-decoration: underline; color: red;}\n";
	    print SAVEFILE "</style></head>\n";

	    print SAVEFILE "<body bgcolor=\"#ffffff\">";

	    print SAVEFILE "<h1>Container summary</h1>";
	    print SAVEFILE "<ul>";
	    foreach my $container (sort keys (%Gear)) {	
		print SAVEFILE "<li> <a href=\"#$container\">$container</a>";
	    }
	    print SAVEFILE "</ul>";
	    print SAVEFILE "<hr>";
	    print SAVEFILE "<h1>Detailed listing</h1>";
	    foreach my $container (sort keys (%Gear)) {		    
		print SAVEFILE "<div class=\"combatant\"><h3><a name=\"$container\">$container</a></h3>\n";
		foreach my $item (sort keys (%{$Gear{$container}})) {
		    $_ = $item;
		    s/ /_/g;
		    print SAVEFILE "<a href=\"http://www.hgwiki.com/wiki/index.php?title=$_\">$item</a>";
		    print SAVEFILE " x$Gear{$container}{$item}" if ($Gear{$container}{$item}>1);
		    print SAVEFILE "<br>";		    
		}
		print SAVEFILE "</div>\n";
	    }

	    print SAVEFILE "<p>This summary was generated by <a href=\"http://highergroundpoa.proboards3.com/index.cgi?board=software&action=display&thread=10946\">NWN-logger</a> v" . $version . " by Claus Ekstroem</p>\n";
	    print SAVEFILE "</body></html>";
	}
	close(SAVEFILE);
    }    
}




sub runlog_start {
    my $fname = shift;
    $current_save_file = $fname // $mw->getSaveFile(-initialfile=> 'lastrun.txt',
				-filetypes=>[['Text files', '.txt'],
					     ['All Files', '*']],
				-defaultextension => '.txt');
    
    if (defined($current_save_file)) {
	open(SAVEFILE, ">$current_save_file");

	# Change the menubuttons so start run is disabled
	$menu_file->entryconfigure('End run', -state=>'normal');
	$menu_file->entryconfigure('Start a run', -state=>'disabled');

	$saverunbuffer = "";
	$log_start_ts = $srv_time if $srv_time; # update timestamp for run-start

	# Initiate a timer that saves the data to the file.
	$savefiletimer = $mw->repeat(10000 => \&runlog_save_buffer);	
    }
}

sub runlog_end {
    runlog_save_buffer();
    close(SAVEFILE);
    $menu_file->entryconfigure('End run', -state=>'disabled');
    $menu_file->entryconfigure('Start a run', -state=>'normal');
    $savefiletimer->cancel;
    undef($saverunbuffer);
    if ($OPTIONS{'autostartrun'}) {
	my $tofile = $mw->getSaveFile(
	    -title => 'Save run-log as ...',
	    -initialfile=> time2str("%Y%m%d_%H%M_", $log_start_ts) . ($last_run || 'HG') . '.txt',
	    -filetypes=>[['Text files', '.txt'],
			 ['All Files', '*']],
	    -defaultextension => '.txt'
	);
	if ($tofile && ($tofile ne $current_save_file)) {
	    copy($current_save_file, $tofile) or print "\nERROR\ncannot copy run-file\n\n";
	}
    }
    $current_save_file = '';
}


sub runlog_save_buffer {
    print SAVEFILE  $saverunbuffer;
    $saverunbuffer="";
}

#
# Function return 1 if the name is considered a party member and 0 otherwise
#
sub partymember {
    my $id = shift @_;
    return 1 if (exists($deaths{$id}) || $id eq $toon);
    return 0;
}


sub new_party_member {
    my $id = shift @_;    
    $deaths{$id} = 0 if !exists($deaths{$id});
    $kills{$id} = 0 if !exists($kills{$id});
    $damage_done{$id} = 0 if !exists($damage_done{$id});
    $swings{$id} = 0 if !exists($swings{$id});
    $badtooncounter{$id} = 0 if !exists($badtooncounter{$id});
    $damage_taken{$id} = 0 if !exists($damage_taken{$id});
    $party{$id} = 1;
}

#
# These function grab information from the general
#
sub toon_kills {
    my $toon = shift;
    if (exists($kills{$toon})) {
	return ($kills{$toon});
    }
    else {
	return 0 ;
    }
}


#
# Configuration functions
#

sub configure_fonts {
    foreach my $colour (@COLS) {
	$damage_out->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]);
	$damage_out->tagConfigure($colour.'Heal', -background => "$colour", foreground => 'black');
	$damage_inc->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]);
	$imms->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font"}, -size => 9]);
	$dmgheader_out->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]);
	$dmgheader_inc->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]);
	$hits_inc->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font-hit"}, -size=>$OPTIONS{"fontsize-hit"}]);
	$hits_out->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font-hit"}, -size=>$OPTIONS{"fontsize-hit"}]);
	$saves->tagConfigure($colour,
				  -font=>[-family=>$OPTIONS{"font-resist"}, -size=>$OPTIONS{"fontsize-resist"}]);
	$resists->tagConfigure($colour,
				  -font=>[-family=>$OPTIONS{"font-resist"}, -size=>$OPTIONS{"fontsize-resist"}]);
	$chatlog->tagConfigure($colour, -foreground=>"$colour");

	$top_info_area->tagConfigure($colour, -foreground=>"$colour");
    } 
}

sub calculate_vulnerabilities {
    my(@damdet);
    my(%damnum);
    for my $detail (keys %dam_taken_detail) {
	my ($mob, $dtype) = split(/ :d: /, $detail);
	my $tdam = $damage_taken{$mob};
	my $cdam = $dam_taken_detail{$detail};

	# If a mob only received 0 damage from element then possibly immune
	if ($cdam==0) {
	    $elemental_immunities{$mob}{$dtype}=1;	    
	}
	next unless $tdam > 0;
	next unless (10 * $cdam) >= $tdam; # Only show if >= 10%
	my $pstr = int(((100 * $cdam) / $tdam) + 0.5);
	push @damdet, "$pstr $dtype $mob";
    }
    for my $outline (sort {  (split(/ /, $b))[0] <=> (split(/ /, $a))[0]} @damdet) {
	my ($pstr, $dtype, $mob) = split(/ /, $outline, 3);
	$damnum{$mob}++;
	if ($damnum{$mob} == 1) {
	    $damage_takenstr{$mob} = "$pstr\% $dtype";
	} elsif ($damnum{$mob} < 4) {
	    $damage_takenstr{$mob} .= ", $pstr\% $dtype";
	}
    }    
}


sub parse_old_log_file {
    my $file = $mw->getOpenFile(-initialfile=> 'oldlogfile.txt',
				-filetypes=>[['Text files', '.txt'],
					     ['All Files', '*']],
				-defaultextension => '.txt');
    
    if (defined($file)) {
	# Halt the automatic parsing
	$parsetimer->cancel;
	my $originalfile = $currentlogfile;
	my $location = tell(LOGFILE);

	$currentlogfile = $file;
	open (LOGFILE, $file);
	parse_log_file();
	close(LOGFILE);
	
	$currentlogfile = $originalfile;
	open (LOGFILE, $currentlogfile);
	seek(LOGFILE, $location, 0);

	# Restart the original parser
	$parsetimer = $mw->repeat($parsetime => \&parse_log_file);
    }
}



#
# The following functions deal with saving and loading/validation of the configuration file
#

sub save_configuration {
    open(CFGFILE, ">$cfgfile") || die "Could not create configuration file";

    # Get the current layout
    $OPTIONS{"geometry"} = $mw->geometry();

    foreach $_ (sort keys(%OPTIONS)) {
        print CFGFILE "$_=$OPTIONS{$_}\n";	
    }
    close(CFGFILE);

    if ($OPTIONS{'autostartrun'}) {
	if (!$current_save_file && ($currentlogfile =~ /^nwclientLog[1-4]\.txt$]/)) {
	    print "autostart run\n";
	    runlog_start('currentrun.txt');
	}
    }
}


sub load_configuration {
    if (-e $cfgfile) {
        open(CFGFILE, "$cfgfile") || die "Could not open configuration file";
        while (<CFGFILE>) {
	    chomp;
	    s/#.*//;
	    s/^\s+//;
	    s/\s+$//;
	    next until length;
	    my ($option, $value) = split(/\s*=\s*/, $_, 2);
	    $OPTIONS{$option} = $value if exists($OPTIONS{$option});
        }
        close(CFGFILE);

	# Validation of the input
        $OPTIONS{"fontsize"} = 9 if ($OPTIONS{"fontsize"}) < 5;
        $OPTIONS{"fontsize"} = 9 if ($OPTIONS{"fontsize"}) >16;
        $OPTIONS{"fontsize-hit"} = 9 if ($OPTIONS{"fontsize-hit"}) < 5;
        $OPTIONS{"fontsize-hit"} = 9 if ($OPTIONS{"fontsize-hit"}) >16;
        $OPTIONS{"fontsize-resist"} = 9 if ($OPTIONS{"fontsize-resist"}) < 5;
        $OPTIONS{"fontsize-resist"} = 9 if ($OPTIONS{"fontsize-resist"}) >16;

	# geometry
	$mw->geometry($OPTIONS{"geometry"}) if ($OPTIONS{"geometry"} ne "");
    }
}

sub update_info_area {
    my ($widget, $options, $def_color) = @_;
    $widget->delete("1.0", 'end');
    my $i = 0;
    for my $opt (@{$options}) {
	$widget->insert('end', " |", $def_color) if $i++;
	if ($opt eq 'server') {
	    $widget->insert('end', " Srv $server", $def_color);
	    if ($uptime_secs) {
		$widget->insert('end', ' up '.time2str("%R", $server_uptime, 0), $def_color); # TODO: change color with uptime
	    }
	}
	elsif ($opt eq 'area') {
	    $widget->insert('end', " $last_run:", $def_color) if $last_run;
	    if ($current_map) { # TODO: && $OPTIONS{'show_area_info'}
		$widget->insert('end', " $current_map", $def_color);
		if ($hg_maps{$current_map}{'respawn'}) {
		    $widget->insert('end', ' '.$hg_maps{$current_map}{'respawn'}, 'red');
		}
	    }
	}
    }
}

sub update_top_info_area {
    update_info_area($top_info_area, ['server', 'area'], '');
}

#
# some helper functions in preparation to using hgdata.xml
#
my %hgmonsters = ();
my %hg_ignore_enemies = ();

sub hg_para_level {
    my $monster = shift;
    if (exists($hgmonsters{$monster})) {
	return $hgmonsters{$monster}{'paragon'} || 0;
    }
    return 0; #exists($PARAMONSTERS{$monster}) ? $PARAMONSTERS{$monster} : 0;
}

sub hg_do_not_hit {
    my $monster = shift;
    # TODO: remove usage of "old" data once we get nohit-flags in xml-data
    return 1 if exists($DONOTHIT{$monster});
    if (exists($hgmonsters{$monster})) {
	return exists($hgmonsters{$monster}{'kb'}); # eq 'Area';
    }
    return 0;
    #return exists($DONOTHIT{$monster});
}

sub hg_ignore_enemy {
    my $monster = shift;
    return exists($hg_ignore_enemies{$monster});
}

sub hg_mob_heals {
    my $monster = shift;
    my $type = shift;
    return 0 if (!exists($hgmonsters{$monster}) || !exists($hgmonsters{$monster}{'heal'}));
    my $h = $hgmonsters{$monster}{'heal'};
    return $type ? $h->{$type} : $h;
}

sub append_monster {
    my ($widget, $monster) = @_;

    my $color = 'white';
    my $flags = '';
    my $heals = '';

    if (exists($hgmonsters{$monster})) {
	my $m = $hgmonsters{$monster};
#print "monster: $monster - ". Dumper($m);
	if (exists($m->{'paragon'})) {
	    my $pl = $m->{'paragon'}; #hg_para_level($monster); # para level
	    $flags .= "P$pl" if $OPTIONS{'showmonsterflags'};
	    $color = ($pl == 1) ? 'yellow' : 'orange';
	}
	if ($m->{'kb'} // $DONOTHIT{$monster}) {
	    $flags .= 'D' if $OPTIONS{'showmonsterflags'};
	    $color = 'red';
	}
	if (exists($m->{'type'})) {
	    $flags .= $m->{'type_short'} if $OPTIONS{'showmonsterflags'};
	    $color = 'pink'; # TODO: color depending on boss-level
	}
	if (exists($m->{'qual'}) && $OPTIONS{'showmonsterflags'}) {
	    $flags .= 'q'.$m->{'qual'};
	}
	if ($flags) {
	    $flags = " [$flags]";
	}
	if (exists($m->{'race'}) && $OPTIONS{'showmonsterrace'}) {
	    $flags = " ($m->{race_short})$flags";
	}
	if (exists($m->{'heals'}) && $OPTIONS{'showmonsterheal'}) {
	    $heals = $m->{'heals'};
	}
    } else {
	$flags = ' (?)' if $OPTIONS{'showmonsterflags'};
    }

    if ($heals) {
	$widget -> insert('end', "$monster$flags", $color);
	$widget -> insert('end', " H: ", 'white');
	my ($el, $proc) = split(/ /, $heals);
	$widget -> insert('end', substr($el,0,1).substr($proc,0,1)."\n", $COLOURS{$el});
    } else {
	$widget -> insert('end', "$monster$flags\n", $color);
    }
}

sub append_attack {
    my ($widget, $ab, $roll, $status, $frequency, $monster, $hitcolor) = @_;

    my $color = (($status =~ /hit|crit/) ? $hitcolor : 'white');
    #$widget -> insert('end', sprintf("%-3d:\t%-4s:\t%2.0f%%:\t%-15s\n", $ab, $status, $frequency, $monster), $color);
    $widget -> insert('end', sprintf("%3d:\t%-4s\t%2.0f%%\t", $ab, $status, $frequency), $color);
    append_monster($widget, $monster);
}

sub append_dmg_line {
    my ($widget, $total, $damage_type, $mob, $heals) = @_;

    my $eso_dmg = 0;
    my $eso_color = '';
    my $eso_show = $OPTIONS{'showesotericdmg'} // 0;
    $eso_show = 0 if $eso_show eq 'no';

	$widget -> insert('end', "$total\t", 'white');
	foreach (@DAMAGETYPES) {
	    if ($DMG_TYPE_ESO{$_}) {
		last if !$eso_show;
		if ($eso_show eq 'sum') {
		    if ($damage_type->{$_}) {
			$eso_dmg += $damage_type->{$_} // 0;
			$eso_color = "$COLOURS{$_}";
		    }
		    next;
		}
	    }
	    if (defined($damage_type->{$_})) {
		if ($heals && $heals->{$_}) {
		    $widget -> insert('end', $damage_type->{$_}, "$COLOURS{$_}Heal");
		    $widget -> insert('end', "\t", "$COLOURS{$_}");
		} else {
		    $widget -> insert('end', $damage_type->{$_} . "\t", "$COLOURS{$_}");
		}
	    } 
	    else {
		$widget -> insert('end', "\t", "$COLOURS{$_}");
	    }
	}

	if ($eso_show eq 'sum') {
	    $widget -> insert('end', ($eso_color ? "$eso_dmg" : '')."\t", $eso_color);
	}

	append_monster($widget, $mob);
}

sub import_hgdata_xml {
    # create object
    my $xml = new XML::Simple;

    # read XML file
    my $data = $xml->XMLin("hgdata.xml");

    # TODO: verify file is ok (check version, ... ?)

    # access XML data
    my $areas = $data->{areas}->{area};
    my $areaname;
    my $area;
    while (($areaname, $area) = each %{$areas}) {

	$hg_areas{$areaname} = {};
	if (exists($area->{'map'})) {
	    #my $maps = $area->{'map'};
	    #printf "found maps in $areaname\n";
	    my $name;
	    foreach $name (keys %{$area->{'map'}}) {
		my @parts = split(/ - /, $name);
		if ($areaname eq $parts[0]) {
		    shift @parts;
		    $name = $parts[0];
		}
		$hg_maps{$name}{'area'} = $areaname;
		#printf "\t$areaname | $name\n";
	    }
	}

	# monster to ignore
	if (exists($area->{ignore})) {
	    my $name;
	    if (exists($area->{ignore}->{name})) {
		$name = $area->{ignore}->{name};
		$hg_ignore_enemies{$name} = 1;
	    } else {
		foreach $name (keys %{$area->{ignore}}) {
		    $hg_ignore_enemies{$name} = 1;
		}
	    }
	}

	# mobs we want to know more about
	next if !exists($area->{mob}) or $areaname eq '*';
	my $mobs = $area->{mob};
	my $mobname;
	my $mob;
	while (($mobname, $mob) = each %{$mobs}) {
	    if (exists($hgmonsters{$mobname})) {
		$hgmonsters{$mobname}{'area'} .= ",$areaname";
		next;
	    }
	    $hgmonsters{$mobname} = $mob;
	    $hgmonsters{$mobname}{'area'} = $areaname;
	    if (exists($mob->{'race'})) {
		$mob->{'race'} =~ /^(\w)(\w)\w+( (\w)\w+)?$/;
		$mob->{'race_short'} = $1 . (defined($4) ? $4 : $2);
	    }
	    if (exists($mob->{'type'})) {
		$mob->{'type'} =~ /^(\w)\w+( (\d))?$/;
		$mob->{'type_short'} = $1;
		$mob->{'type_short'} .= $3 if defined($3);
	    }
	    if (exists($mob->{'qual'}) && ($mob->{'qual'} =~ /^(\d)\.0$/)) {
		$mob->{'qual'} = $1; # strip ".0" from end of qual if it's there
	    }
	    if (exists($mob->{'heals'})) {
		my ($el, $proc) = split(/ /, $mob->{'heals'});
		$mob->{'heal'}{$el} = $proc;
	    }
	}
    }

    my $ignore_maps = $data->{ignoremaps}{'map'};
    while (($areaname, $area) = each %{$ignore_maps}) {
	$hg_maps{$areaname}{'area'} = '';
    }
}
