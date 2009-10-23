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

use File::Copy; # for copying the runfile on run-end

use subs qw/beep/;
use warnings;
use strict;

my $version = "0.1.4b";
# some container vars to take over the countless globals
my %YAL;
my %YW = (); # YAL Widgets

my %emptyRun; # blueprint for run-data, filled with hg_run_init()
my %currentRun; # data collection for current run
my $RUN = \%currentRun; # run data (hits, kills, dmg, ...)
my $runData; # = $$RUN{data}; # run data of individual actors (mobs or party members)}

my (%HGdata, $HGmobs, $HGareas, $HGmaps, $HGtoons, $HGnew);
yal_init();

my $shamelessadvertising = 0;

# ills hacking my $YW{othertimers};

my $debug = 0;

#
# The following hashes keeps most of the information
#

my %AB = ();
my %MinAC = ();
my %MaxAC = ();
my %SR = ();
my %TR = ();

#
# The following hashes are more detailed and contain information split on attacker and defender. everything should eventually go into those as the program evolves
#
my %Saves = ();
my %AbilityChecks = ();
my %SkillChecks = ();

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
                   "Fire" => "red",
                   "Cold" => "lightblue",
                   "Sonic" => "orange",
                   "Magical" => "pink",
                   "Divine" => "yellow",
                   "Positive Energy" => "white",
                   "Positive" => "white",
                   "Negative Energy" => "darkgray",
                   "Negative" => "darkgray",
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
$YW{mw} = new MainWindow();
$YW{mw} ->title("NWN logger v" .$version . ". --- by Claus Ekstrom 2008. Edits by Illandous & Separ");

#
# Now define the main frames/areas of the GUI
# The GUI is split into 3 areas: a panel on the rhs and the "main" bit which is split into an upper and lower panel
#
$YW{frm_top} = $YW{mw} -> Frame();
$YW{frm_bottom} = $YW{mw} -> Frame(-label=>"Spell/turning resists and saves");
$YW{frm_menu} = $YW{mw} -> Frame(-relief=>'raised', -borderwidth=>2)  -> pack(-side=>'top', -fill=>'x');


# Set up the menu bar
$YW{menu_view} = $YW{frm_menu} -> Menubutton(-text=>'View', 
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

$YW{menu_party} = $YW{frm_menu} -> Menubutton(-text=>'Party',
					 -underline=>0,
					 -tearoff => 'no',
					 -menuitems => [['command' => "~Party setup",
							 -command=>\&dialog_party_entry],
							['command' => "~Clear party",
							 -command=>\&clear_party]]) -> pack(-side=>'left');


$YW{menu_options} = $YW{frm_menu} -> Menubutton(-text=>'Options', 
					   -underline=>0,
					   -tearoff => 'no',
					   -menuitems => [['command' => "~Preferences", 
							   -command => \&dialog_program_options],
							  [Separator => ''],
							  ['command' => "~Reset all stats", 
							   -command => \&yal_reset_all]]) -> pack(-side=>'left');

$YW{menu_file} = $YW{frm_menu} -> Menubutton(-text=>'File', 
					-underline=>0,
					-tearoff => 'no',
					-menuitems => [['command' => "Save ~HTML summary",
							-command => \&yal_save_summary_html],
						       [Separator => ''],
							['command' => "~Start a run",
							 -command => \&runlog_start],
						       ['command' => "E~nd run",
							 -command => \&runlog_end,
							 -state => 'disabled'],
						       ['command' => "~Parse old log file", 
							-command => \&parse_old_log_file],
						       ['command' => "Save ~inventories", 
							-command => \&yal_save_inventories]
						       ]) -> pack(-side=>'left');

$YW{l_mod_date} = $YW{frm_menu} -> Label(-text=>'Mod.Build: ?') -> pack(-side=>'right');

## Top info frame: name, current server, uptime, logfile info
$YW{frm_info} = $YW{frm_top} -> Frame();
$YW{frm_info} -> pack(-side=>'top', -anchor=>'w', -fill=>'x');
$YW{frm_name} = $YW{frm_info} -> Frame() ->pack(-side=>'top');
$YW{toon_name} = $YW{frm_info} -> LabEntry(-textvariable => \$$RUN{toon},
				    -label => "Name",
				    -labelPack => [-side => 'left']) -> pack(-side=>'left');
$YW{newlog} = $YW{frm_info} -> Button(-text => "Next", -command =>\&yal_inc_logcount, -padx => 3, -pady => 1)->pack(-side=>"right");
$YW{frm_logfile} = $YW{frm_info} -> Frame() ->pack(-side=>'top');
$YW{logfile_text} = $YW{frm_info} -> LabEntry(-textvariable => \$YAL{logfile_info},
				    -label => "Log:",
				    #-width => 5, # increase if we want to show seconds
				    -state => 'disabled', -disabledforeground => 'black',
				    -labelPack => [-side => 'left']) -> pack(-side=>'right');
$YW{top_info_area} = $YW{frm_info} -> Text(-width=>60, -height=>1, 
				    -foreground=>'white', -background=>'black',
				    -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}])->pack(-side=>"top", -fill=>"x", -expand=>0);


## Fugue timers
$YW{frm_rightbar} = $YW{mw} -> Frame();
$YW{frm_killdeath} = $YW{frm_rightbar} -> Frame(-relief=>'groove', -borderwidth=>2, -background=>"black") -> pack(-side=>'bottom', -fill=>'x');
$YW{frm_othertimers} = $YW{frm_rightbar} -> Frame(-label=>"Timers", -relief=>'groove', -borderwidth=>2, -background=>"black") -> pack(-side=>'bottom', -fill=>'x');
$YW{othertimers} = $YW{frm_othertimers} -> Scrolled('Text', -width=>17, -height=>8, 
				       -foreground=>'white', -background=>'black',
				       -scrollbars=>'s', -wrap=>'none', -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]) -> pack(-side=>'bottom', -fill=>'both', -expand=>1);
$YW{othertimers}->tagConfigure("none", -foreground => "red");
$YW{othertimers}->tagConfigure("dispelled", -foreground => "orange");
$YW{othertimers}->tagConfigure("casting", -foreground => "blue");

$YW{frm_dynamicwindow} = $YW{frm_rightbar} -> Frame(-label=>"Hit Counter", -relief=>'groove', -borderwidth=>2);
$YW{frm_dynamicwindow} -> Label(-textvariable => \$$RUN{hits}, -foreground=>$col_cold, -background=>"black") ->pack(-fill =>'x');

$YW{frm_dynamicdamageheaders} = $YW{frm_rightbar} -> Frame(-label=>"Hit Counter", -relief=>'groove', -borderwidth=>2);
$YW{frm_dynamicdamageheaders} -> Label(-textvariable => \$$RUN{hits}, -foreground=>$col_cold, -background=>"black") ->pack(-fill =>'x');

$YW{frm_fugue} = $YW{frm_rightbar} -> Frame(-label=>"Fugue timers", -relief=>'groove', -borderwidth=>2) -> pack(-side=>'top', -fill=>'both', -expand=>1);

$YW{fuguetimers} = $YW{frm_fugue}->Scrolled('Text', -width=>17, -height=>10, 
				       -foreground=>'white', -background=>'black',
				       -scrollbars=>'s', -wrap=>'none', -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]) -> pack(-side=>'top', -fill=>'both', -expand=>1);

$YW{fuguetimers}->tagConfigure("critical", -foreground => "red");
$YW{fuguetimers}->tagConfigure("warning", -foreground => "pink");
# use other colors for our own toon so we better see it
$YW{fuguetimers}->tagConfigure("self", -foreground => "yellow");
$YW{fuguetimers}->tagConfigure("criticalself", -foreground => "black", -background => 'red');
$YW{fuguetimers}->tagConfigure("warningself", -foreground => "red");

#start ills hacking                                                                       _______________


## Character status
$YW{frm_char} = $YW{mw} -> Frame(-relief=>'ridge', -borderwidth=>2);

$YW{frm_kills} = $YW{frm_killdeath} -> Frame(-relief=>'groove', -borderwidth=>2, -background=>"black") -> pack(-side=>'top', -fill=>'x');
$YW{frm_deaths} = $YW{frm_killdeath} -> Frame(-relief=>'groove', -borderwidth=>2) -> pack(-side=>'top', -fill=>'x');

$YW{frm_kills} -> Label(-textvariable => \$$RUN{lastKilled}, -foreground=>"white", -background=>"black") ->pack(-side=>'bottom', -fill=>'x');
$YW{frm_kills} -> Label(-text => 'Kills: ', -foreground=>$col_acid, -background=>"black") ->pack(-side=>'left');
$YW{frm_kills} -> Label(-textvariable => \$$RUN{kills}, -foreground=>$col_acid, -background=>"black") ->pack();

$YW{frm_deaths} -> Label(-textvariable => \$$RUN{lastKiller}) ->pack(-side=>'bottom', -fill=>'x');
$YW{frm_deaths} -> Label(-text => 'Deaths: ', -foreground=>$col_fire) ->pack(-side=>'left');
$YW{frm_deaths} -> Label(-textvariable => \$$RUN{deaths}, -foreground=>$col_fire) ->pack();


$YW{conceal_lab} = $YW{frm_char} -> Label(-text => "Conceal");

$YW{saves} = $YW{frm_bottom} -> Scrolled('Text', -width=>60, -height=>4, 
				      -foreground=>'white', -background=>'black',
				      -font => [-family => $OPTIONS{"font-resist"}, -size=>$OPTIONS{"fontsize-resist"}],
				      -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'right', -fill=>'both', -expand=>1);
$YW{resists} = $YW{frm_bottom} -> Scrolled('Text', -width=>60, -height=>4, 
				      -foreground=>'white', -background=>'black',
				      -font => [-family => $OPTIONS{"font-resist"}, -size=>$OPTIONS{"fontsize-resist"}],
				      -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'right', -fill=>'both', -expand=>1);


$YW{resists}->tagConfigure("darkgray", -foreground => "darkgray");
$YW{resists}->tagConfigure("lightblue", -foreground => "lightblue");
$YW{resists}->tagConfigure("yellow", -foreground => "yellow");
$YW{resists}->tagConfigure("red", -foreground => "red");
$YW{resists}->tagConfigure("green", -foreground => "green");
$YW{othertimers}->tagConfigure("casts", -foreground => "orange");
$YW{saves}->tagConfigure("lightblue", -foreground => "lightblue");
$YW{saves}->tagConfigure("yellow", -foreground => "yellow");


#$resist -> Subwidget("text") -> tagConfigure("darkgray", -foreground => "darkgrey");

#
# Make a dummy label
#
$YW{frm_inc} = $YW{frm_top} -> Frame(-label => "Incoming damage:") -> pack(-side=>"top", -anchor=>"w", -fill=>"both", -expand=>1);
$YW{frm_out} = $YW{frm_top} -> Frame(-label => "Outgoing damage:") -> pack(-side=>"top", -anchor=>"w", -fill=>"both", -expand=>1);

$YW{hits_inc} = $YW{frm_inc} -> Scrolled('Text', -width=>35, -height=>6, 
				      -foreground=>'white', -background=>'black',
				      -tabs => [$OPTIONS{"fontsize-hit"}*5], # screen distance sucks on my laptop -tabs => [qw/.3i/],
				      -font => [-family => $OPTIONS{"font-hit"}, -size=>$OPTIONS{"fontsize-hit"}],
				      -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'left', -fill=>"both", -expand=>1);

$YW{frm_inc_header} = $YW{frm_inc} -> Frame() -> pack(-side=>'right', -fill=>"both", -expand=>1);

$YW{dmgheader_inc} = $YW{frm_inc_header} -> Text(-width=>60, -height=>1, 
				      -foreground=>'white', -background=>'black',
				      -tabs => [$OPTIONS{"fontsize"}*3.5], # screen distance sucks on my laptop -tabs => [qw/.35i/],
				      -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}])->pack(-side=>"top", -fill=>"x", -expand=>0);

$YW{damage_inc} = $YW{frm_inc_header} -> Scrolled('Text', -width=>60, -height=>6, 
				      -foreground=>'white', -background=>'black',
				      -tabs => [$OPTIONS{"fontsize"}*3.5], # screen distance sucks on my laptop -tabs => [qw/.35i/],
				      -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}],
			              -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'top', -fill=>"both", -expand=>1);

$YW{hits_out} = $YW{frm_out} -> Scrolled('Text', -width=>35, -height=>6, 
				      -foreground=>'white', -background=>'black',
				      -tabs => [$OPTIONS{"fontsize-hit"}*5], # screen distance sucks on my laptop -tabs => [qw/.3i/],
				      -font => [-family => $OPTIONS{"font-hit"}, -size=>$OPTIONS{"fontsize-hit"}],
				      -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'left', -fill=>'both', -expand=>1);

$YW{frm_out_header} = $YW{frm_out} -> Frame() -> pack(-side=>'right', -fill=>"both", -expand=>1);
$YW{dmgheader_out} = $YW{frm_out_header} -> Text(-width=>60, -height=>1, 
				      -background=>'black',
				      -tabs => [$OPTIONS{"fontsize"}*3.5], # screen distance sucks on my laptop -tabs => [qw/.35i/],
				      -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}])->pack(-side=>"top", -fill=>"x", -expand=>0);

$YW{damage_out} = $YW{frm_out_header} -> Scrolled('Text', -width=>60, -height=>6, 
				      -foreground=>'white', -background=>'black',
				      -tabs => [$OPTIONS{"fontsize"}*3.5], # screen distance sucks on my laptop -tabs => [qw/.35i/],
				      -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}],
			              -scrollbars=>'e', -wrap=>'none') -> pack(-side=>'top', -fill=>"both", -expand=>1);

# Now insert the headers _if_ the headers are desired
$YW{dmgheader_inc} -> insert('end', "Tot\t", "white");
$YW{dmgheader_out} -> insert('end', "Tot\t", "white");
foreach $_ (@DAMAGETYPES) {
    $YW{dmgheader_inc} -> insert('end',  substr($_,0,3) . "\t",  "$COLOURS{$_}");
    $YW{dmgheader_out} -> insert('end',  substr($_,0,3) . "\t",  "$COLOURS{$_}");
}



##
$YW{frm_status} = $YW{mw} -> Frame();
$YW{bt_show_imms} = $YW{frm_status} -> Button(-text => "Show", -padx => 3, -pady => 0) -> pack(-side => "right");
# logfile info moved to top right
#my $YW{newlog}     = $YW{frm_status} -> Button(-text => "New Log File", -command =>\&yal_inc_logcount)->pack(-side=>"right");
$YW{imms} = $YW{frm_status} -> Text(-background=>"black", -height=>1, width=>70, -tabs => [qw/.23i/],
				     -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]) -> pack(-side=>"right");
$YW{l_status_msg} = $YW{frm_status} -> Label(-textvariable => \$YAL{statusmessage}, -borderwidth=>2, -relief=>'groove', -anchor=>"w") ->pack(-side=>"left", -fill => 'x', -expand=>1);


##
## Geometry management
##
$YW{frm_status} -> pack(-side=>'bottom', -anchor=>'w', -fill=>'x');
$YW{frm_rightbar}  -> pack(-side=>"right", -fill => 'y', -anchor=>'n');
$YW{frm_top} -> pack(-side=>'top', -expand=>1, -fill => 'both');
$YW{frm_bottom} -> pack(-side=>'top', -expand=>1, -fill => 'both');



$YAL{parsetimer} = $YW{mw}->repeat($YAL{parsetime} => \&parse_log_file);
# This is really a poor mans version of the timers. A potential problem is the time NWN takes to write stuff to the log - espcially on network drives
# It would be much smarter to continuously adjust the timers according to the log time. I may get around to that at some point
$YAL{rpDeathTimers} = $YW{mw}->repeat(1000 => \&update_death_timers);   
$YAL{rpEffectsTimers} = $YW{mw}->repeat(1000 => \&update_effects_timers);

#
# Make sure that the party selection page is listed when the program starts
#
# $YW{mw}->after(1 => \&dialog_party_entry);



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

yal_load_config();
dialog_chat_log();   # Setup the chat log 
configure_fonts();   

hgdata_import_xml(); # test ... replace upper call when ready

gui_print_immunities();
if ($OPTIONS{'autostartrun'}) {
    runlog_start('currentrun.txt');
}


open(LOGFILE, "$YAL{currentlogfile}");

MainLoop;
# yal_save_config();
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

    return if !(-e $YAL{currentlogfile});

    # Make sure we're parsing the active log file

    # logfile- and run-info is now top-right
    $YAL{logfile_info} = $YAL{currentlogfile} . (defined($YAL{saverunbuffer}) ? ' (RUN)' : '');
    $YAL{statusmessage} = "Total XP: " . num_fmt($$RUN{totalxp}) . " | Total dmg: " . (num_fmt($$runData{$$RUN{toon}}{damOut}) || "None yet" ) ;

    if ($OPTIONS{"showparagons"}==1) {
	if ($$RUN{totalmobkills}>0) { 
	    my $numberofparagons = ($$RUN{paracount}{1} // 0) + ($$RUN{paracount}{2} // 0) + ($$RUN{paracount}{3} // 0);
	    $YAL{statusmessage} .= " | Paragons: " . int($numberofparagons/$$RUN{totalmobkills} *1000)/10 . "%";
	}
	else {
	    $YAL{statusmessage} .= " | Paragons: 0%";
	}
    }
        
    my $endhitout = ($YW{hits_out} -> yview())[1];
    my $endhitinc = ($YW{hits_inc} -> yview())[1];
    my $enddmgout = ($YW{damage_out} -> yview())[1];
    my $enddmginc = ($YW{damage_inc} -> yview())[1];
    my $endsaves  = ($YW{saves} -> yview())[1];
    my $endresists= ($YW{resists}-> yview())[1];

    # Clear the EOF flag
    seek(LOGFILE,0,1) || ($YAL{statusmessage} .= " | Log file not found!");
    while(<LOGFILE>) {
	if (defined($YAL{saverunbuffer})) {
	    $YAL{saverunbuffer} .= $_ ;
	}

	if (/^\s*$/) { # skip empty lines
	    parse_sm_end() if $YAL{parseSM};
	    next;
	}

	# Remove DOS line shifts if any. Old habit
	s/\015\012/\012/;
	# drop the initial bit
	s/\[CHAT WINDOW TEXT\]\s+//;
	my $time;
	if (s/^\[([^\]]+)\]\s//) {
	    $time = $1; # if defined $1;
	}

	# update server uptime if we did catch it once
	if ($time // 0) {
	    # my($dow, $mon, $day, $hr, $min, $sec) = $time =~ /(\S+) (\S+) (\d+) (\d+):(\d+):(\d+)/;
	    my $new_time = str2time($time) || 0;
	    $$RUN{logFirstTS} = $new_time if !$$RUN{logFirstTS}; # remember first parsed timestamp
	    if ($new_time != $$RUN{srvLogTS}) {
		# current second actually changed
		$$RUN{srvLogTS} = $new_time;
		#print "$time -> " . str2time($time) . ", uptimeat|\n" if ($time);
		if ($$RUN{srvBaseUptime}) {
		    $$RUN{srvUptime} = $$RUN{srvBaseUptime} + ($$RUN{srvLogTS} - $$RUN{srvBaseTS});
		    my $current_round = int $$RUN{srvUptime} / 6;
		    gui_update_top_info_area();
		    if ($current_round != $$RUN{srvRound}) {
			# every 6 seconds we have a new round
			#printf "new round: %d -> %d @ %d - %s\n", $$RUN{srvRound}, $current_round, $$RUN{srvUptime}, time2str("%R", $$RUN{srvUptime}, 0);
			$$RUN{srvRound} = $current_round;
		    }
		}
	    }

	    # if we got a timestamp all parsing submodes are finished
	    parse_sm_end(); # $YAL{parseSM} = '';
	}
	elsif (/^  / && $YAL{parseSM}) {
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

	# Different timers. Missing a lot of stuff here. Imm force for example
	# GR
	if (/^Greater Sanctuary will be available again in 150 seconds/) {
	    start_timer($YAL{timerGSanct}, 150) if $YAL{isCurrent};
	    next;
	}
	if (/Greater Smite will be available again in (\d+) seconds/) {	   
	    start_timer($YAL{timerGSmite}, $1) if ($1 >= 120) && $YAL{isCurrent};  # Make sure only to start timer if it's the first occurrence
	    next;
	}


	# Saves, skill and ability checks
	next if parse_checks_and_saves();


	# Spell and turning resists
	# Never got round to including turn resists
	if (/^(.+) casts (.+)$/) {
            my $who = $1;
	    if ($2 =~ /unknown spell/) {
		next if $OPTIONS{'skipunknownspells'};
		if ($OPTIONS{"otherspells"} && ($who ne $$RUN{toon})){  
		    $YW{resists} -> insert('end',$_, 'darkgray');
		}
	    }
	    else {
		if ($OPTIONS{"ownspells"} && ($1 eq $$RUN{toon})) {
		    #make sure it is a effect that we have seen
		    if (exists $YAL{effectTimersMax}{$2}) {
			# TODO: find out if extend spell screws this
			$YAL{effectTimers}{$2} = $YAL{effectTimersMax}{$2};
		    }
		    $YW{resists} -> insert('end',$_, 'casts');
		}
		elsif ($OPTIONS{"otherspells"} && ($1 ne $$RUN{toon})){  
		    $YW{resists} -> insert('end',$_, 'white');
		}
	    }
	    next;
	}	
	next if (/^(.+) casting (.+)$/);

	# Spell penetration: our toon tried to beats an enemies SR
	if (/^(.+) : Spell Penetration : \*(success|failure)\* : \((\d+) \+ (\d+) .+ vs. SR: (\d+)\)$/) {
	    $YW{resists} -> insert('end', "SP: $1 : ", 'lightblue');
	    if ($2 eq "success") {
		$YW{resists} -> insert('end', "*$2*", 'green');
	    }
	    else {
		$YW{resists} -> insert('end', "*$2*", 'red');
	    }
	    $YW{resists} -> insert('end', " : $3 + $4 = " . ($3 + $4) . " vs. SR: $5 ", 'lightblue');

	    # List the spell penetration percentage if that is desired
	    if ($OPTIONS{"sppercent"}==1) {
		$YW{resists} -> insert('end', "(" .(21 - (max(1, min(20, ($5 - $4)))))*5 . "%)"."\n", 'yellow');
	    }
	    else {
		$YW{resists} -> insert('end', "\n");
	    }

	    if (exists($SR{$1})) {
		$SR{$1} = $5 if ($5>$SR{$1});
	    }
	    else {
		$SR{$1} = $5;
	    }
	    next;	   
	}

	# an attacker tries to beat our SR
	if (/^(.+) : Spell Resistance : \*(defeated|success)\* : (.+)$/) {
	    #$YW{resists} -> insert('end',$_, 'lightblue');
	    $YW{resists} -> insert('end', "SR *$2* $3: $1\n", 'lightblue');
	    next;
	}

	# Turning
	if (/^(.+) : Turn (Outsider|Construct|Vermin|Undead) : \*(success|failure)\* : \((\d+) \+ (\d+) .+ vs. TR: (\d+)\)$/) {
	    $YW{resists} -> insert('end', "Turn $2: $1 : *$3* : ($4 + $5 = " . ($4 + $5) . " vs. SR: $6 (" . (21 - (max(1, min(20, ($6 - $5)))))*5 . '%)'."\n", 'lightblue');

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
	if (/^(.+) : Immune to (.+?)\.?$/) {
	    $$runData{$1}{immuneTo}{$2} = 1;
	    # TODO: display somewhere if $1 is our current target
	    next;
	}
	#if (/^(.+) : Immune to (.+)$/) {
	#    $immune{$1}{$2} = 1;	    
	#    next;
	#}	

	# more output from !list imm
	if (/^(Spell|Other) immunities:$/) {
	    $YAL{parseSM} = "imm$1";
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
	    $YAL{effectTimers} = {};
	    next;
	}
	if (/Your Eternal Return spell fires, preventing the life from leaving your body!/) {
	    clear_last_fugue_timer();
	    $YAL{effectTimers} = {};
	    next;
	}

	# meta-data (server, party members, ...)
	next if parse_collect_metadata();

	#ills dispelelling routine
	#if (/^.+\*dispelled\*.+$/){
	if (/^(.+) : Dispel (.+) : \*dispelled\* :(.+)$/) {

	    if ($$RUN{toon} eq $1) {
		$YW{resists} -> insert('end',"Your $2 has been dispelled \n", 'orange');
		#print "your $2 dispelled \n";
		#print $YAL{effectTimers}{$2};
		delete $YAL{effectTimers}{$2};
	    }
	    next;
	}

	#
	# Effects 
        #
	# This one registers who the effects concern and clears effects timers so they can be regenerated
	if (/^\[Server\] Effects on (.+):/) {
	    $YAL{effectTimers} = {};

	    $YAL{effectId} = $1;
	    $YAL{effectId} = $$RUN{toon} if ($1 eq "you");

	    $YAL{parseSM} = 'effects';
	    next;
	}

	# check if a list of gear follows
	next if parse_gear_list_header();

	# Loot split rolls for whiners. Not sure what I will do with it yet
	if (/(.+) rolled a \[D(4|6|8|10|12|20|100)\] and got a: \[(\d+)\]\./) {
	    
	}	

	# Clear all effects timers after rest
	if (/^Done resting\.$/) {
	    $YAL{effectTimers} = {};
	}

	# Messages regarding entering and leaving the server
	#next if (/(.+) has left as a player\.\./);
	#next if (/(.+) has joined as a player\.\./);
	next if (/(.+) has (joined|left) as a player\.\./);

	# area specific lines - for now only hells
	# TODO: if ($$RUN{cArea} =~ /^Hells/)
	next if parse_line_area_Hells();

        # Yay!
        if (/You are flooded with an incredible sense of well-being!/) {           
	    $YW{saves} -> insert('end',$_, 'yellow');
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
	if (/\Q$$RUN{toon}\E: Send me to (Dis|Minauros|Phlegethos|Stygia|Malbolge|Maladomini|Cania|Nessus)/) {
	    if ($OPTIONS{"hellentrymessagebox"}==1) {
		my $clear_stats = $YW{mw}->messageBox(-message => "Clear stats?",
						  -title => "Entering hells",
						   -type => "yesno", -icon => "question");		
		if ($clear_stats eq "Yes") {
		    yal_reset_all();
		} 
	    }
	    next;
	}

	#
	# Different ingame commands to control program
	#
	next if parse_player_cmds();

	if ($time && s/^\[Server\] //) {
	    parse_srv_msg($_);
	    next;
	}

	# TODO: some more things we could catch and display in info area
	# if (/You are in Higher Ground Enhanced Mode./)
	if (/^Latest Module Build: (.*)\s*/) {
	    $$RUN{srvModDate} = $1;
	    $YW{l_mod_date}->configure(-text=>"Mod.Build: $1");
	    next;
	}

	print "Line not parsed : $_" if ($debug ne 0);
    }

    if ($OPTIONS{"fixscroll"} == 1) {
	$YW{resists}->see('end');
	$YW{saves}->see('end');
	$YW{hits_out}->see('end');
	$YW{hits_inc}->see('end');
	$YW{damage_out}->see('end');
	$YW{damage_inc}->see('end');
    }

    # Always scroll to bottom if the window was at bottom before. Bugs under windows?    
    $YW{resists}->see('end') if $endresists == 1;
    $YW{saves}->see('end')  if $endsaves == 1;
    $YW{hits_out}->see('end') if $endhitout == 1;
    $YW{hits_inc}->see('end') if $endhitinc == 1;
    $YW{damage_out}->see('end') if $enddmgout == 1;
    $YW{damage_inc}->see('end') if $enddmginc == 1;

    # Check if it's time to change log files
    yal_check_log_file();
}

# saves and ability checks
sub parse_checks_and_saves {

    # ability checks
    if (/^(.+) : (Strength|Dexterity|Constitution|Intelligence|Wisdom|Charisma) vs. (.+) : \*(success|failure|success not possible)\* : (.+ vs\. DC: (\d+).)/) {
	$AbilityChecks{$3}{$2} = $6;
	#$YW{saves} -> insert('end',$_, 'lightblue');
#print "ability check for [$1]\n" if ($1 ne $$RUN{toon});
	$YW{saves} -> insert('end', "STAT $2 *$4* $5 vs. $3\n", 'lightblue');
	return 1;
    }

    #if (/^(.+) : (Will|Fortitude|Reflex) Save : /) {
    if (/^(.+?)( : .+)? : (Will|Fortitude|Reflex) Save : \*(.*)\* : (.*)/) {
	if ($1 eq $$RUN{toon}) {
	    $YW{saves} -> insert('end', "SAVE $3 *$4* $5".($2 // '')."\n", 'white');
	} else {
	    $YW{saves} -> insert('end',$_, 'white');
	}
	return 1;
    }

    #if (/^(.+) : (Will|Fortitude|Reflex) Save vs. (.+) : \*(success|failure)\* : \(\d+ \+ (\d+) = \d+ vs\. DC: (\d+)\)$/) {
    if (/^(.+?)( : .+)? : (Will|Fortitude|Reflex) Save vs. (.+) : \*(success|failure)\* : (\(\d+ \+ (\d+) = \d+ vs\. DC: (\d+)\))$/) {
	if ($$RUN{toon} eq $1) {
	    #$YW{saves} -> insert('end',$_, 'white');
	    $YW{saves} -> insert('end', "SAVE $3 vs. $4 *$5* $6".($2 // '')."\n", 'white');
	}
	else {
	    chomp;
	    $YW{saves} -> insert('end',$_, 'lightblue');
	    if ($OPTIONS{"dcpercent"}==1) {
		#$YW{saves} -> insert('end', " (" .((max(1, min(20, (($6-1) - $5)))))*5 . "%)"."\n", 'yellow');
		$YW{saves} -> insert('end', " (" .((max(1, min(20, (($8-1) - $7)))))*5 . "%)"."\n", 'yellow');
	    } else {
		$YW{saves} -> insert('end',"\n");
	    }
	}
	#$Saves{$1}{$2}{"min"}{$3} = $5 if (!exists($Saves{$1}{$2}{"min"}{$3}));
	#$Saves{$1}{$2}{"max"}{$3} = $5 if (!exists($Saves{$1}{$2}{"max"}{$3}));
	#$Saves{$1}{$2}{"min"}{$3} = $5 if $5 < $Saves{$1}{$2}{"min"}{$3};
	#$Saves{$1}{$2}{"max"}{$3} = $5 if $5 > $Saves{$1}{$2}{"max"}{$3};
	$Saves{$1}{$3}{"min"}{$4} = $7 if (!exists($Saves{$1}{$3}{"min"}{$4}) || ($7 < $Saves{$1}{$3}{"min"}{$4}));
	$Saves{$1}{$3}{"max"}{$4} = $7 if (!exists($Saves{$1}{$3}{"max"}{$4}) || ($7 > $Saves{$1}{$3}{"max"}{$4}));
#print "save: n='$1', s='$3', ?='$4', v='$7'\n";
	return 1;
    }

    #if (/^(.+) : (Discipline|Concentration|Taunt|Bluff) vs. (.+) : \*(success|failure|success not possible)\* : .+ vs\. DC: (\d+)/) {
    if (/^(.+) : (Discipline|Concentration|Taunt|Bluff)( vs. (.+))? : \*(success|failure|success not possible)\* : (.+ vs\. DC: (\d+).)/) {
	# TODO: rework collecting saves and stuff
	$SkillChecks{$3}{$2} = $7 if $3; #$5;
	if ($$RUN{toon} eq $1) {
	    #$YW{saves} -> insert('end',$_, 'white');
	    $YW{saves} -> insert('end', "SKILL $2 *$5* $6".($3 // '')."\n", 'white');
	} else {
	    $YW{saves} -> insert('end',$_, 'lightblue');
	}
	return 1;
    }

    # Skills
    if (/^(.+) : (.+) vs\. (.+) : \*(success|failure)\* : /) {
	# if ($1 eq $$RUN{toon})
	$YW{saves} -> insert('end',$_, 'yellow');
	return 1;
    }
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
		$YW{t_chatlog}->insert('end', $_, 'purple');
	    }
	    elsif (($speakername =~ /^\s*$/) && /Interserver (\w+) message from (.*) \((.*)\): (.*)/) {
		my %channelcolors = ('newbie' => 'darkgray', 'bazaar' => 'red');
		$YW{t_chatlog}->insert('end', "$2 ($3)");
		$YW{t_chatlog}->insert('end', "[".ucfirst($1)."]: $4\n", $channelcolors{$1});
	    }
	    else {
		$YW{t_chatlog}->insert('end', $_, 'green');
	    }

	}
	elsif ($type eq ("Shout")) {
	    if (($speakername eq 'SERVER') && /Run forming on( this)? server( \d+)?\. Contact (.*) \((.*)\) if interested: (.*)/) {
		my ($toon, $player, $srv, $msg) = ($3, $4, $2 // '', $5);
		$srv =~ s/^ /@/ if $srv;
		$YW{t_chatlog}->insert('end', "$toon ($player)$srv");
		$YW{t_chatlog}->insert('end', "[RUN]: $msg\n", 'orange');
	    } else {
		$YW{t_chatlog}->insert('end', $_, 'yellow');		
	    }
	}
	else {
	    $YW{t_chatlog}->insert('end', $_);
	    # Remember to code this person as a potential party member if in party talk
	    #to be taken out when list of players is defined
	    new_party_member($speakername) if (/\[Party\]/);
	}
	$YW{t_chatlog}->see('end');
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

	my $oAtt = $$runData{$attacker} // hg_run_new_actor($attacker);
	my $oDef = $$runData{$defender} // hg_run_new_actor($defender);

	$$oAtt{damOut} += $total;                   # sum for attacker
	$$oDef{damIn} += $total;                  # sum for defender
	$$RUN{damEnemy}{$attacker}{$defender} += $total;        # stores attacker and defender
	
	my $meleehit = 0;
	$meleehit = 1 if ($damages =~ /\d+ Physical/); # TODO: find out if we catch bigby spells here

	# get mob healing info if attacker is a party member
	my $heals = partymember($attacker) ? hg_mob_heals($defender) : 0;

	# Now make sure to keep information about which damage types that are actually doing damage
	# Stole this idea and code from Kins. Ty :)
	my %damage_type = ();
	while ($damages =~ s/(\d+) (\S+)\D*//) {
	    my ($damount, $dtype) = ($1, $2);
	    # TODO: if ($heals{$dtype}) ...
	    $damage_type{$dtype} = $damount;
	    $$oAtt{damOutTypes}{$dtype} = 1 if ($meleehit==1);
	    $$RUN{dam_taken_detail}{$defender . " :d: " . $dtype} += $damount;
	}
	
	# General data was saved above
	# Now we should handle the specific damage data that is shown on the GUI
	return 1 unless ($attacker eq $$RUN{toon} || $defender eq $$RUN{toon});
	
	if ($$RUN{toon} eq $attacker) {
	    append_dmg_line($YW{damage_out}, $total, \%damage_type, $defender, $heals);
	}
	else {
	    append_dmg_line($YW{damage_inc}, $total, \%damage_type, $attacker, 0);
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
    if (/(.+ \: )?(.+) attempts (Cleave|Great Cleave|Knockdown|Improved Knockdown|Disarm|Improved Disarm|Melee Touch Attack|Ranged Touch Attack|Called Shot\: Arm|Called Shot\: Leg|Whirlwind Attack) on (.+) : \*(hit|miss|critical hit|parried|target concealed: (\d+)%|resisted)\* : \((\d+) \+ (\d+)/) {
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

	my $killer = $$runData{$1} // hg_run_new_actor($1);
	my $killed = $$runData{$2} // hg_run_new_actor($2);

	$$killer{kills}++;
	$$killer{lastKilled} = $2;
	$$killed{deaths}++;
	$$killed{lastKiller} = $1;
	$$RUN{killsEnemy}{$1}{$2}++;

	if (exists($$RUN{partyList}{$2})) {
	    # Start a death timer if it was a party member who died
	    push(@{$$RUN{deathTimers}{300}}, $2); # unless $$RUN{cMap} && !$HGmaps->{$$RUN{cMap}}{'respawn'};
	    # was it our own toon?
	    if ($2 eq $$RUN{toon}) {
		# if it was the toon that died ... clear effects timers
		$$RUN{deaths}++;
		$$RUN{lastKiller} = $1;
		$YAL{effectTimers} = {};
	    } 
	}
	else {
	    # Check if the monster was a paragon
	    $$RUN{totalmobkills}++;
	    my $pl = hg_para_level($2);
	    $$RUN{paracount}{$pl}++ if ($pl);
	}

	# Hmm. Still counting this separately for the player. That is not necessary. Should be integrated with the general hash
	if ($$RUN{toon} eq $1) {
	    $$RUN{kills}++;
	    $$RUN{lastKilled} = $2;
	}

	return 1;
    }

    # XP
    if (/^Experience Points Gained:\s+(\d+)$/ ) {
	$$RUN{totalxp} += $1;
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
	
	if (exists($HGmaps->{$name})) {
	    $$RUN{cArea} = $HGmaps->{$name}{'area'} // ''; # default: no area
	} else {
	    $HGmaps->{$name}{'new'} = 1;
	    $$RUN{cArea} = '';

	    my @parts = split(/ - /, $name);
	    if ($#parts) {
		if (exists($HGareas->{$parts[0]})) {
		    $$RUN{cArea} = $parts[0];
		}
		elsif ($parts[0] =~ /(Avernus|Dis|Minauros|Phlegethos|Stygia|Malbolge|Maladomini|Cania|Nessus)/) {
		    $$RUN{cArea} = $1;
		    $HGareas->{$1} = {area => 'Hells', new => 1};
		}
	    }

	    if (!$$RUN{cArea}) {
		@parts = split(/ /, $parts[0]); # $name);
		$$RUN{cArea} = $parts[0] if $#parts && exists($HGareas->{$parts[0]});
	    }

	    $HGmaps->{$name}{'area'} = $$RUN{cArea};
	}

	$$RUN{cMap} = $name;
	# remember pvp-status of map
	$HGmaps->{$name}{'pvp'} = $pvp;

	# which run are we doing?
	$$RUN{lastRun} = $$RUN{cArea} if $$RUN{cArea};
    }

    # area status: fugue/limbo/... ?
    elsif (/^You will (.*) if you respawn in this area\.$/) {
	$HGmaps->{$$RUN{cMap}}{'respawn'} = $1 if ($$RUN{cMap});
    }

    # update demi count
    #elsif (/^The last spawn in this area was affected by (\d+) demi iterations\.$/) {
    #}

    # switch mode to collecting immunities
    elsif (/^Damage immunities:$/) {
	$YAL{parseSM} = 'imm';
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
	#$YAL{parseSM} = 'acc'
    #}

    # !list ac
    #elsif (/^Armor class:/) {
    #}

    # !list saves
    #elsif (/^Saving throws:/) {
    #}

    # !list spknown
    #elsif (/^Your known spells:/) {
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
    if ($YAL{parseSM}) {
	my $fn = "parse_sm_$YAL{parseSM}";
	#print "sub func found: $fn - $_\n" if (defined(&$fn));
	goto &$fn if (defined(&$fn));
    }
    return 0;
}

# end of data for a sub-mode parser
sub parse_sm_end {
    if ($YAL{parseSM}) {
	#print "submode end: $YAL{parseSM}\n";
	my $fn = "parse_sm_end_$YAL{parseSM}";
	goto &$fn if (defined(&$fn));
	$YAL{parseSM} = '';
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
	gui_print_immunities(); # TODO: only once when we have all of them
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

# collect data for effects
sub parse_sm_effects {
    if(/^    \#(\d+) (.+) \[((\d+)m)?(\d+)s.+\]/) {
	my ($eNumId, $effectName, $eTimeStr) = ($1, $2, ($3 // '')."$5s");
	my $eTimeLeft = (($4 // 0) * 60) + $5;

	#removes the old one if it exists, and then puts the new one in place
	if (exists $YAL{effectTimers}{$effectName}) {
	    delete $YAL{effectTimers}{$effectName};
	}

	# no need to start timers when parsing an old logfile
	if ($YAL{isCurrent}) {
	    $YAL{effectTimers}{$effectName} = $eTimeLeft;
	    # TODO: only save max if self-cast ? take max from new and old if avail
	    $YAL{effectTimersMax}{$effectName} = $eTimeLeft;
	}

	# This only work on yourself atm
	$$runData{$YAL{effectId}}{effects}{"$effectName $eNumId"} = $eTimeStr;
	return 1;
    }
}

#######################################################################
# meta-data collecting (server, party, location, ...)

sub parse_collect_metadata {

    # If you use the PC Scry then set that toon as the primary
    if (/^(.+): PCScry: Select an option$/) {
	if ($OPTIONS{"catchtoonname"}==1) {
	    $$RUN{toon} = $1;
	    new_party_member($1);
	}
	return 1;
    }

    # Welcome message
    if (/Welcome to Higher Ground, (.+)!$/) {
	if ($OPTIONS{"catchtoonname"}==1) {
	    # clear old toon from party if re-login with another toon
	    $$RUN{partyList}{$$RUN{toon}} = 0 if ($$RUN{toon} and defined $$RUN{partyList}{$$RUN{toon}});

	    $$RUN{toon} = $1;
	    new_party_member($1);
	}
	return 1;
    }

    # !who header - clears party stats
    if (/^\[Server\] ===== Server (\d+).+$/){
	$YAL{parseSM} = 'who';
	#$$RUN{partyList} = {};
	if ($1 eq $$RUN{srvName}) {
	    $YAL{myServerWho} = 1;
	    clear_party() if $YAL{catchPartyWho}; # only if it's a party-who
	} else {
	    $YAL{myServerWho} = 0;
	    $YAL{catchPartyWho} = 0;
	}
	return 1;
    }

    # On which server are we? - at welcome and end of !who
    if (/You are on server (\d+)/) {
	$$RUN{srvName} = $1;
	$YAL{myServerWho} = 0; # no !who output to follow immediately after
	$YAL{catchPartyWho} = 0;
	return 1;
    }

    # prepare server uptime display
    if (/This server has been up for ((\d+) hours, )?(\d+) minutes,? and (\d+) seconds\./) {
	$$RUN{srvBaseUptime} = $4 + 60*$3 + ($2 ? 3600*$2 : 0);
	$$RUN{srvBaseTS} = $$RUN{srvLogTS};
	return 1;
    }

    if (/^(.+) has (joined|left) the party\./) {
	if ($2 eq "joined") {
	    new_party_member($1); # TODO: make option for this catch
	} else {
	    $$RUN{partyList}{$1} = 0;
	    $$RUN{toonList}{$1} = 1;
	}
	return 1;
    }

    return 0;
}

# Player information from !who commands
sub parse_sm_who {

    return 1 if (!$YAL{myServerWho}); # ignore playerlisting from other servers

    # old if (/^  \s*\[\d+(\/\d+)?\]( \|.+\|)? (.+) $/) {
    #ills version: if (/^.+\[(\d+ \D\D\D.+?)\] (.+) $/){    
    if (/^.+\[(\d+ \D\D\D.+?)\] (.+) $/) {
	chomp;
	my $toonname = $2;

	# Remove DM tag
	$toonname =~ s/ \[(DM|Guide) PC\]$//;
	# Remove guild tag
	#removed, done with regex
	    #$toonname =~ s/ <.+>//;

	$$RUN{toonList}{$toonname} = 1; #0 if (!defined($$RUN{toonList}{$toonname}));
	new_party_member($toonname) if ($YAL{catchPartyWho});
    }
    return 1;
}

#######################################################################
# collect gear listings
sub parse_gear_list_header {
    # From uses of !list contents on a container

    # Loot lines and rarity - skip "Common" and "Uncommon" stuff
    if (/(.+): (Non-random|Beyond Ultrarare|Ultrarare|Rare) items:/) {
	# TODO: if ($$RUN{toon} eq $q) ...
	$YAL{gearcontainer} = $1;
	#if ($YAL{parseSM} ne 'gear') {
    print "reset gearcontainer $YAL{gearcontainer}\n" if (exists($YAL{gear}{$YAL{gearcontainer}}) && !$YAL{next_item_rarity});
	    # Now clear the existing data if that exists
	    $YAL{gear}{$YAL{gearcontainer}} = {} if (exists($YAL{gear}{$YAL{gearcontainer}}) && !$YAL{next_item_rarity});
	    $YAL{parseSM} = 'gear';
	#}
	$YAL{next_item_rarity} = $2; # TODO: use that data
    }
    elsif (/\[Server\] Contents of Persistent (Transfer|Storage) Chest:/) {
	$YAL{gearcontainer} = "Bankchest $YAL{bankchest}";
	$YAL{parseSM} = 'gear';
	# Now clear the existing data if that exists
	delete $YAL{gear}{$YAL{gearcontainer}}; # = () if (exists($YAL{gear}{$YAL{gearcontainer}}));
	$YAL{next_item_rarity} = ''; # unknown rarity
    }
    elsif (/You are now using bank chest '(.+?)'/) {
	$YAL{bankchest} = $1;
    }
    elsif (/You are now using your default bank chest/) {
	$YAL{bankchest} = "default";
    }
    else {
	return 0;
    }

    return 1;
}

# collect gear data from "!list inventory" or "!list contents"
sub parse_sm_gear {
    if (/^    ([A-Za-z].+)/) {
	if ($YAL{gearcontainer} ne "") {
	    $YAL{gear}{$YAL{gearcontainer}}{$1}++;
	}
	# TODO: if ($YAL{next_item_rarity}) ...
	return 1;
    }
}

sub parse_sm_end_gear {
    return if ($YAL{next_item_rarity} && /^\s*$/); # items of other rarity may follow
    $YAL{parseSM} = '';
}

#######################################################################
# area specific stuff - for now only hells
#

# Specific hell comments
# Not sure what to use those for atm
sub parse_line_area_Hells {
    if (/^(Asmodeus stuns you with Malbolge's Strike|The malebranche's wing buffet knocks you to the ground|Asmodeus smites you with Maladomini's Ruin|Asmodeus infects you with Avernan Ague|The brood worm siphons some of your magical energies, and strikes you mute with awe|The erinyes has entangled you|The malebranche performs a whirl, catching you on its blade|The malebranche snatches you up and drops you, but you glide back to the ground|The pit fiend's wing buffet knocks you down|The pit fiend calls down a meteor swarm)!$/) {
	$YW{saves} -> insert('end',$_, 'yellow');
	return 1;
    }
    if (/The Amnizu has stricken you with amnesia!/) {
	$YW{saves} -> insert('end',$_, 'yellow');
	# TODO: remember amni until rest
	return 1;
    }
    if (/^(.+) : Restore Hells Penalties/) {
	#print "GR: by '$1' @ $$RUN{srvUptime}/$$RUN{srvRound}\n";
	# TODO: start counting rounds
	return 1;
    }

    return 0;
}

# player commands to control YAL
sub parse_player_cmds {
    if (/\Q$$RUN{toon}\E: \[Whisper\] \.(.+)/) {
	my $command = $1;
	if ($command eq "clear" || $command eq "reset") {
	    yal_reset_all();
	}
	elsif ($command eq "pstats") {
	    dialog_party_summary();
	}
	elsif ($command eq "who") {
	    $YAL{catchPartyWho} = 1;
	}

	return 1;
    }
}

#######################################################################
# Processing functions

#
# process attack data
#
sub process_attack {
    my ($attacker, $defender, $attacktype, $roll, $ab, $status) = @_;

    my $oAtt = $$runData{$attacker} // hg_run_new_actor($attacker);
    my $oDef = $$runData{$defender} // hg_run_new_actor($defender);

    $$oAtt{swingsOut}++;
    $$oDef{swingsIn}++;
    $$RUN{swingsAt}{$attacker}{$defender}++;
    
    # Make sure to update the AB and AC estimate
    $AB{$attacker} = 0 if (!exists($AB{$attacker}));
    $AB{$attacker} = $ab if ($ab > $AB{$attacker});
    
    if ($status eq "hit" || $status eq "crit") {
	$$oAtt{hits}++;
	$$RUN{hitsEnemy}{$attacker}{$defender}++;

	if ($status eq "crit") {
	    $$oAtt{crits}++;
	    $$RUN{critsEnemy}{$attacker}{$defender}++;
	}
	
	$$RUN{hits}++ if ($attacker eq $$RUN{toon});
	if ($roll<20) {
	    if ((!exists($MinAC{$defender})) || ($ab+$roll < $MinAC{$defender})) {
		$MinAC{$defender} = $ab+$roll;
	    }
	}

	# special attacks
	# TODO: this can't be all ...
	$$RUN{disarms}{$attacker}{$defender}++ if ($attacktype =~ /disarm/i);
    }
    elsif ($status eq "miss" && $roll>1) {
	$$oDef{dodge}++;
	$MaxAC{$defender} = 0 if (!exists($MaxAC{$defender}));
	$MaxAC{$defender} = $ab+$roll if ($ab+$roll > $MaxAC{$defender});
    }
    elsif ($status =~ /(\d+)\%/) {
	return if $status eq '100%'; # anti-exploit, not real conceal, so skip it
	$$oDef{dodge}++;
	$$oDef{conceal} = $1 if (!exists($$oDef{conceal}));
	$$oDef{conceal} = $1 if $1 > $$oDef{conceal};
	$$RUN{missConcealed}{$attacker}{$defender}++;
	$status = "c$1%"; # for better display?
    }
    else {
	# 'miss' | 'resisted'
	$$oDef{dodge}++;
    }

    $$oAtt{hitPercentage} = sprintf("%3.2f %%", $$oAtt{hits}/$$oAtt{swingsOut}*100);
    
    if ($OPTIONS{"badboy"}==1) {
	$$oAtt{badToonHits}++ if (hg_do_not_hit($defender));
    }
    
    if ($$RUN{toon} eq $attacker) {
	$$RUN{hit_frequency} = ($YAL{hit_frequency_weight}*$$RUN{hit_frequency})/($YAL{hit_frequency_weight} + 1);
	if ($status eq "hit" || $status eq "crit" ) {
	    $$RUN{hit_frequency} += 1/($YAL{hit_frequency_weight} + 1);
	}
	append_attack($YW{hits_out}, $ab, $roll, $status, $$RUN{hit_frequency}*100, $defender, 'green');
    }
    elsif ($$RUN{toon} eq $defender) {
	$$RUN{defence_frequency} = ($YAL{hit_frequency_weight}*$$RUN{defence_frequency})/($YAL{hit_frequency_weight} + 1);
	if ($status ne "hit" && $status ne "crit" ) {
	    $$RUN{defence_frequency} += 1/($YAL{hit_frequency_weight} + 1);
	}
	append_attack($YW{hits_inc}, $ab, $roll, $status, $$RUN{defence_frequency}*100, $attacker, 'red');
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
    $YW{othertimers}->delete("1.0", 'end');
    
    #Create ordered listing of effect times sorted by time
    my @sortedEffects = sort {$YAL{effectTimers}{$a} <=> $YAL{effectTimers}{$b}} keys %{ $YAL{effectTimers} };
    foreach my $EffectName (@sortedEffects){
	#print "$EffectName $YAL{effectTimers}{$EffectName}\n";
	#decrement the value on each hash
	#delete timer if it is 0

	$YAL{effectTimers}{$EffectName}--;
	if ($YAL{effectTimers}{$EffectName} <= 0) {
	    delete $YAL{effectTimers}{$EffectName};
	    next;
	}

	#format the effect to to window
	my $etimertext = sprintf "%2d:%02d %s \n", integer_div($YAL{effectTimers}{$EffectName}, 60), ($YAL{effectTimers}{$EffectName} % 60), $EffectName;

	#place the effect in the window
	$YW{othertimers} -> insert('end', $etimertext);
    }
    @sortedEffects = {};
}

sub update_death_timers {
    $YW{fuguetimers}->delete("1.0", 'end');
	#$YW{othertimers}->delete("1.0", 'end');
	
    if (exists($$RUN{deathTimers}{0})) {
	delete($$RUN{deathTimers}{0});
    }
    foreach my $time (sort {$a <=> $b} keys(%{ $$RUN{deathTimers} })) {	
	$$RUN{deathTimers}{$time-1} =[@{$$RUN{deathTimers}{$time}}];
	if ($time<11 && $OPTIONS{"fuguebeep"}) {
	    $YW{mw} -> bell;
	}
	foreach my $player (@{$$RUN{deathTimers}{$time}}) {
	    my $timertext = sprintf "%2d:%02d %s \n", integer_div($time, 60), ($time % 60), $player;
	    my $s = ($player eq $$RUN{toon}) ? 'self' : '';
	    if ($time<10) {
		$YW{fuguetimers} -> insert('end', $timertext, "critical$s") ;
	    }
	    elsif ($time<30) {
		$YW{fuguetimers} -> insert('end', $timertext, "critical$s") ;
	    }
	    elsif ($time<60) {
		$YW{fuguetimers} -> insert('end', $timertext, "warning$s"); 
	    }
	    else {
		$YW{fuguetimers} -> insert('end', $timertext, $s);
	    }
	}
	delete($$RUN{deathTimers}{$time});
    }
}


sub clear_last_fugue_timer() {
#    pop(@{$$RUN{deathTimers}{300}});        
}


sub integer_div {
    my ($a, $b) = @_;
    return(($a - ($a % $b)) / $b);
}

sub min {
    my ($a, $b) = @_;
    return ($a > $b) ? $b : $a;
}

sub max {
    my ($a, $b) = @_;
    return ($a > $b) ? $a : $b;
}

# format int number with thousand seperator
sub num_fmt {
    my $n = shift;
    $n =~ s/\d{1,3}(?=(\d{3})+(?!\d))/$&,/g if $n;
    return $n;
}

sub yal_inc_logcount {
    $YAL{logfilenumber}++; 
    $YAL{logfilenumber} = 1 if ($YAL{logfilenumber}>4);

    $YAL{currentlogfile} = "nwclientLog". $YAL{logfilenumber} .".txt";

    close(LOGFILE);
    open(LOGFILE, "$YAL{currentlogfile}");
}

sub gui_print_immunities {
    $YW{imms} -> delete("1.0", 'end');
    # Remove physical
    foreach (@DAMAGETYPESIMM) {
	my $t = $immunities{$_};
	# TODO: make option if to show resists
	$t .= '|' . $resists{$_} if ($resists{$_});
	#$YW{imms} -> insert('end',  $immunities{$_}. "\t", "$COLOURS{$_}");
	$YW{imms} -> insert('end',  $t. "\t", "$COLOURS{$_}");  
    }
}


#
# Check if we should update the current log file
#
sub yal_check_log_file {
    # Find the next logfile name
    my $nextlogfile = "nwclientLog". ($YAL{logfilenumber}+1) .".txt";
    if ($YAL{logfilenumber}>3) {
	$nextlogfile = "nwclientLog1.txt";	
    }

    # Check if the next file exists and if it has a newer timestamp than the current file
    if (-e $nextlogfile) {	
	return yal_inc_logcount() if ((-M $nextlogfile) <= (-M $YAL{currentlogfile}));
    }
}


#
# This hasn't been updated in some time. Probably not resetting everything correctly but then I never use it anyway
#
sub yal_reset_all {
    $$RUN{deaths} = 0;
    $$RUN{kills} = 0;
    $$RUN{totalxp} = 0;
    $$RUN{lastKilled}="";
    $$RUN{lastKiller}="";

    $YAL{timerGSanct} = [];
    $YAL{timerGSmite} = [];

    $$RUN{hit_frequency} = 0;
    $$RUN{defence_frequency} = 0;

    $$RUN{toonList} = {};

    hg_run_reset(); # TODO: check this ...

    $YW{damage_inc}->delete("1.0", 'end');
    $YW{damage_out}->delete("1.0", 'end');
    $YW{hits_inc}->delete("1.0", 'end');
    $YW{hits_out}->delete("1.0", 'end');   
    $YW{saves}->delete("1.0", 'end');
    $YW{resists}->delete("1.0", 'end');   
}


sub clear_party {
    $$RUN{partyList} = {};
    $$RUN{partyList}{$$RUN{toon}} = 1 if $$RUN{toon};
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
		my @existingparty = keys(%{$$RUN{partyList}});
		if ($debug) {print "@existingparty \n";
	}
	$party_dialog = $YW{mw}->Toplevel();
#	$party_dialog->attributes(-topmost=>1);
	$party_dialog->title("Party member setup");

	$party_dialog->LabEntry(-textvariable => \$$RUN{toon},
				-label => "Own character",
				-labelPack => [qw/-side left -anchor w/]) -> pack();

	for (my $i=2; $i<=10; $i++) {
	    # Fill up the choises with existing party members	    
	    if (@existingparty) {
		$_ = shift(@existingparty);
		$_ = shift(@existingparty) if ($_ eq $$RUN{toon});
		$pty{$i} = $_;
	    }

	    my $thistoon = $party_dialog->BrowseEntry(-variable => \$pty{$i},
				       -label => "Member $i");

	    foreach $_ (sort { $$RUN{toonList}{$b} <=> $$RUN{toonList}{$a} || $a cmp $b } keys %{$$RUN{toonList}}) {
		$thistoon->insert("end", $_);
	    }	    
	    $thistoon-> pack(-anchor=>'e');

	}
	$party_dialog->Button(-text => "Ok",
			      -command => sub { $party_dialog->withdraw();
						$party_dialog->grabRelease();
						clear_party();
						new_party_member($$RUN{toon});
						for (my $i=2; $i<=10; $i++) {
						    if (defined($pty{$i})) {
							if ($pty{$i} ne "" && !exists($$RUN{partyList}{$pty{$i}})) {
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

	$party_summary = $YW{mw}->Toplevel();
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
	foreach my $id (sort (keys(%{$$RUN{partyList}}))) {	    

	    # TODO: check if it's an active partymember or was just logged on in between
	    $col = 0;
	    $row++;
	    my $pm = $$runData{$id};

	    $ps_frm->Label(-text => $id, -relief => 'ridge')
		    ->grid(-row => $row, -column => $col++, -sticky => 'nswe');
	    $ps_frm->Label(-textvariable => \$$pm{kills}, -relief => 'ridge', -font => $pfont)
		    ->grid(-row => $row, -column => $col++, -sticky => 'nswe');
	    $ps_frm->Label(-textvariable => \$$pm{lastKilled}, -relief => 'ridge', -font => $pfont)
		    ->grid(-row => $row, -column => $col++, -sticky => 'nswe');
	    $ps_frm->Label(-textvariable => \$$pm{deaths}, -relief => 'ridge', -font => $pfont)
		    ->grid(-row => $row, -column => $col++, -sticky => 'nswe');
	    $ps_frm->Label(-textvariable => \$$pm{lastKiller}, -relief => 'ridge', -font => $pfont)
		    ->grid(-row => $row, -column => $col++, -sticky => 'nswe');
	    $ps_frm->Label(-textvariable => \$$pm{damOut}, -relief => 'ridge', -font => $pfont)
		    ->grid(-row => $row, -column => $col++, -sticky => 'nswe');
	    $ps_frm->Label(-textvariable => \$$pm{hitPercentage}, -relief => 'ridge', -font => $pfont)
		    ->grid(-row => $row, -column => $col++, -sticky => 'nswe');
	    $ps_frm->Label(-textvariable => \$$pm{badToonHits}, -relief => 'ridge', -font => $pfont)
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
	$options_dialog = $YW{mw} -> Toplevel();
	$options_dialog->title("Options");
	
	# Place OK button at bottom
	$options_dialog->Button(-text => "Ok",
				-command => sub { $options_dialog->withdraw();
						  yal_save_config();
						  configure_fonts();
					      }) -> pack(-side=>'bottom');

	my $fontsetup = $options_dialog -> Frame(-label =>"Fonts", -relief=>'ridge', -borderwidth=>2)  -> pack(-side=>'top', -fill=>'x');       

        # Fonts
	my $fontcfg_dmg = $fontsetup -> Frame() -> pack(-side=>'top', -fill=>'x');
        my $fontlist = $fontcfg_dmg->BrowseEntry(-label => "Damage windows", -variable=>\$OPTIONS{"font"}, -labelPack=>[-side=>'top'])->pack(-side=>'left');
	$fontlist->insert('end', sort $YW{mw}->fontFamilies);
#	$fontsetup->Label(-text=>"Font size:")->pack();
	$fontcfg_dmg->Scale( -orient=>'horizontal', -width=>20, -from=>5, -to=>16,
				-showvalue=>1, -variable=>\$OPTIONS{"fontsize"} )->pack(-side=>'left', -anchor=>'s');

	my $fontcfg_hits = $fontsetup -> Frame() -> pack(-side=>'top', -fill=>'x');
        my $fontlisthit = $fontcfg_hits->BrowseEntry(-label => "Hit windows", -variable=>\$OPTIONS{"font-hit"}, -labelPack=>[-side=>'top']) -> pack(-side=>'left');
	$fontlisthit->insert('end', sort $YW{mw}->fontFamilies);
	$fontcfg_hits->Scale( -orient=>'horizontal', -width=>20, -from=>5, -to=>16,
				-showvalue=>1, -variable=>\$OPTIONS{"fontsize-hit"} )->pack(-side=>'left', -anchor=>'s');


	my $fontcfg_resist = $fontsetup -> Frame()  -> pack(-side=>'top', -fill=>'x');
        my $fontlistresist = $fontcfg_resist->BrowseEntry(-label => "Resist/saves windows", -variable=>\$OPTIONS{"font-resist"}, -labelPack=>[-side=>'top']) -> pack(-side=>'left');
	$fontlistresist->insert('end', sort $YW{mw}->fontFamilies);
	$fontcfg_resist->Scale( -orient=>'horizontal', -width=>20, -from=>5, -to=>16,
				-showvalue=>1, -variable=>\$OPTIONS{"fontsize-resist"} )->pack(-side=>'left', -anchor=>'s');

	my $viewsetup = $options_dialog -> Frame(-label =>"View", -relief=>'ridge', -borderwidth=>2)  -> pack(-side=>'top', -fill=>'x');
	$viewsetup->Checkbutton(-text => "Display hit counter", 
				     -variable => \$OPTIONS{"hitcounter"},
				     -command => sub { 
					 if ($OPTIONS{"hitcounter"} == 1) {
					     $YW{frm_dynamicwindow} -> pack(-side=>'bottom', -fill=>'x');
					 } else {
					     $YW{frm_dynamicwindow} -> pack('forget');					     
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
	$details_dialog = $YW{mw} -> Toplevel();
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

	# TODO: add elemental immunities
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
	#@critterlist{(keys(%{$$RUN{partyList}}), keys(%kills), keys(%deaths))} = ();
	@critterlist{(keys(%{$runData}))} = ();
	foreach $_ (sort keys %critterlist) {

	    next if !$_; # TODO: find out why we get an empty key

	    $grid->add($_);
	    if (exists($$RUN{partyList}{$_})) {
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

	    if (exists($$runData{$_}{conceal})) {
		$grid->itemCreate($_, 3, -text => $$runData{$_}{conceal});
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
	    
	    $grid->itemCreate($_, 5, -text => $$runData{$_}{kills});
	    $grid->itemCreate($_, 6, -text => $$runData{$_}{deaths});

	    # Immunities
	    my $imm = "";
	    $imm .= "Cr " if (exists($$runData{$_}{immuneTo}{"Critical Hits"}));
	    $imm .= "Sn " if (exists($$runData{$_}{immuneTo}{"Sneak Attacks"}));
	    $imm .= "Mi " if (exists($$runData{$_}{immuneTo}{"Mind Affecting Spells"}));
	    $imm .= "B7 " if (exists($$runData{$_}{immuneTo}{"Bigby's Grasping Hand"}));
	    $imm .= "Im " if (exists($$runData{$_}{immuneTo}{"Implosion"}));
	    $imm .= "DM " if (exists($$runData{$_}{immuneTo}{"Death Magic"}));
	    $grid->itemCreate($_, 7, -text => $imm);


	    $grid->itemCreate($_, 9, -text => $$runData{$_}{damInStr});
	}

    }
    else {
	$details_dialog->deiconify();
	$details_dialog->raise();	
    }
}


sub dialog_chat_log {
    # We only want one copy of this window
    if (!Exists($YW{dlg_chatlog})) {
	$YW{dlg_chatlog} = $YW{mw} -> Toplevel();
	$YW{dlg_chatlog}->withdraw();
	$YW{dlg_chatlog}->title("Chat summary");
	$YW{dlg_chatlog}->protocol('WM_DELETE_WINDOW' => sub { $YW{dlg_chatlog}->withdraw() });  # Capture the destroy icon

	
	$YW{dlg_chatlog}->Button(-text => "Ok",
				-command => sub { $YW{dlg_chatlog}->withdraw();
					      }) -> pack(-side=>'bottom');
	
	$YW{t_chatlog} = $YW{dlg_chatlog} -> Scrolled('Text', -width=>60, -height=>4, 
					       -foreground=>'white', -background=>'black',
					       -font => [-family => $OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}],
					       -scrollbars=>'e', -wrap=>'word', -spacing1=>2
						) -> pack(-side=>'top', -fill=>'both', -expand=>1);       	
    }
    else {
	$YW{dlg_chatlog}->deiconify();
	$YW{dlg_chatlog}->raise();	
    }
}


sub dialog_effects {
    my $effectsdialog;

    # We only want one copy of this window
    if (!Exists($effectsdialog)) {
	$effectsdialog = $YW{mw} -> Toplevel();
	$effectsdialog->title("Summary of effects");

	my $whichtoon;
	my $showeffects;

        my $toonchooser = $effectsdialog->BrowseEntry(-label => "Toons:", -variable=>\$whichtoon, 
						      -browsecmd=> sub {
							  if (exists($$runData{$whichtoon}{effects})) {
							      $showeffects->delete("1.0", 'end');
							      foreach my $effect (sort keys(%{ $$runData{$whichtoon}{effects} })) {
								  
								  $showeffects->insert('end', $effect . "\t" . $$runData{$whichtoon}{effects}{$effect}.  "\n");
							      }
							  }
						      }, 
						      -state=> 'readonly',
						      -labelPack=>[-side=>'top'])->pack(-side=>'top');
	$toonchooser->insert('end', sort keys(%{ $$RUN{partyList} })); #sort keys(%Effects));


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


sub yal_save_summary_html {
    my $file = $YW{mw}->getSaveFile(-initialfile=> 'lastrun.html',
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
	foreach my $id (sort (keys(%{$$RUN{partyList}}))) {
	    print SAVEFILE "<li> <a href=\"#$id\">$id</a>";
	}
	print SAVEFILE "</ul>";
	
	print SAVEFILE "<hr>";
	print SAVEFILE "<h1>Party summary</h1>";
	print SAVEFILE "<table border=1>";
	print SAVEFILE "<tr><th bgcolor=lightgray>Name</th><th bgcolor=lightgray>Kills</th><th bgcolor=lightgray>Deaths</th><th bgcolor=lightgray>Damage taken</th><th bgcolor=lightgray>Damage done</th>";
	print SAVEFILE "<th bgcolor=lightgray title=\"Overall hit percentage and 95% confidence interval\">Hit \%</th><th bgcolor=lightgray title=\"Overall dodge percentage and 95% confidence interval\">Dodge \%</th><th bgcolor=lightgray title=\"Number of swings against hell monsters with nasty party kb\">Holla score</th></tr>";
	foreach my $id (sort (keys(%{$$RUN{partyList}}))) {	    
	    print SAVEFILE "<tr><td>$id</td>";
	    print SAVEFILE "<td align=right>$$runData{$id}{kills}</td>";
	    print SAVEFILE "<td align=right>$$runData{$id}{deaths}</td>";
	    print SAVEFILE "<td align=right>$$runData{$id}{damIn}</td>";
	    print SAVEFILE "<td align=right>$$runData{$id}{damOut}</td>";
	    if (exists($$runData{$id}{hitPercentage})) {
		my $ptilde = ($$runData{$id}{hits}+2) / ($$runData{$id}{swingsOut}+4);
		my $se = sqrt($ptilde*(1-$ptilde)/($$runData{$id}{swingsOut}+4));
		print SAVEFILE "<td align=left>$$runData{$id}{hitPercentage} (" . int(($ptilde-1.96*$se)*1000)/10 . " - " . int(($ptilde+1.96*$se)*1000)/10 .")</td>";
	    }
	    else {
		print SAVEFILE "<td align=center>-</td>";
	    }
	    if (exists($$runData{$id}{dodge}) & exists($$runData{$id}{swingsIn})) {
		my $dodgechance = 100*($$runData{$id}{dodge} / $$runData{$id}{swingsIn});
		my $ptilde = ($$runData{$id}{dodge}+2) / ($$runData{$id}{swingsIn}+4);
		my $se = sqrt($ptilde*(1-$ptilde)/($$runData{$id}{swingsIn}+4));
		printf SAVEFILE "<td align=left>%5.2f (%5.2f - %5.2f)</td>", $dodgechance, int(($ptilde-1.96*$se)*1000)/10, int(($ptilde+1.96*$se)*1000)/10;
	    }
	    else {
		print SAVEFILE "<td align=center>-</td>";
	    }
	    print SAVEFILE "<td align=right>" . ($$runData{$id}{badToonHits} // " -") . "</td></tr>";
	}
	print SAVEFILE "</table>";
	
	if ($$RUN{totalmobkills}>0) { 
	    my $numberofparagons = (exists($$RUN{paracount}{1}) ? $$RUN{paracount}{1} : 0) + (exists($$RUN{paracount}{2}) ? $$RUN{paracount}{2} : 0) + (exists($$RUN{paracount}{3}) ? $$RUN{paracount}{3} : 0);
	    print SAVEFILE "<p title=\"Percentage of killed monsters that were paragons\">Paragon percentage: " . int($numberofparagons/$$RUN{totalmobkills} *1000)/10 . "% ";
	    if ($numberofparagons>0) {
		print SAVEFILE "(" . (exists($$RUN{paracount}{1}) ? $$RUN{paracount}{1} : 0);
		print SAVEFILE "/" . (exists($$RUN{paracount}{2}) ? $$RUN{paracount}{2} : 0) . "/";
		print SAVEFILE (exists($$RUN{paracount}{3}) ? $$RUN{paracount}{3} : 0) . ")";		
	    }
	}

	print SAVEFILE "<hr>";
	print SAVEFILE "<h1>Detailed report</h1>\n";
	my %critterlist;
	#@critterlist{(keys(%{$$RUN{partyList}}), keys(%kills), keys(%deaths))} = ();
	@critterlist{(keys(%{$runData}))} = ();
	foreach $_ (sort keys %critterlist) {

	    next if !$_; # TODO: this shouldn't happen - find out why

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
	    printf SAVEFILE "Max conceal: %4.0f<br>", ($$runData{$_}{conceal} // 0);
	    print SAVEFILE "Kills: $$runData{$_}{kills}<br>";
	    printf SAVEFILE "Deaths: %4d<br>", ($$runData{$_}{deaths} // 0);

	    printf SAVEFILE "<p><p>";
	    printf SAVEFILE "Swings/hits/crits dealt:<br> %4.0f/%4.0f/%4.0f<br>", ($$runData{$_}{swingsOut} // 0), ($$runData{$_}{hits} // 0), ($$runData{$_}{crits} // 0);

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

	    print SAVEFILE "<p><div class=\"immBox\"><b>Immunities:</b><font size=-2><br>", (exists($$runData{$_}{immuneTo}) ? join(", ", sort (keys(%{$$runData{$_}{immuneTo}}))) : "-") . "</font></div>";
	    printf SAVEFILE "<p><div class=\"vulnBox\" title=\"The box lists the most common damage types that were taken\"><b>Damage taken:</b><br>%s<br></div>", exists($$runData{$_}{damInStr}) ? join("<br>",split(/, /, $$runData{$_}{damInStr})) : "";

	    printf SAVEFILE "<p><div class=\"vulnBox\" title=\"The box lists the elements/exotics that this mob might be immune to. Note this is influenced by non-resistable damage\"><b>Damage immunity:</b><br>%s<br></div>", (exists($$HGmobs{$_}{immsEl}) ? join("<br>",sort(keys(%{$$HGmobs{$_}{immsEl}}))) : "");
	    
	    printf SAVEFILE "<p><div class=\"vulnBox\" title=\"Guesstimate of damage types done when you are hit by this PC/monster\"><b>Damage types dealt:</b><br>%s<br></div>", exists($$runData{$_}{damOutTypes}) ? join("<br>", keys %{ $$runData{$_}{damOutTypes} } ) : "No clue";

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
	    @defenderlist{(keys(%{$$RUN{killsEnemy}{$_}}), keys(%{$$RUN{damEnemy}{$_}}), keys(%{$$RUN{swingsAt}{$_}}))}  = ();
	    foreach my $defender (sort keys %defenderlist) {
		print SAVEFILE "<tr><td>$defender</td>";
		print SAVEFILE "<td align=right>" . ($$RUN{killsEnemy}{$_}{$defender} // "") . "</td>";

		print SAVEFILE "<td width=10%><table border=0><tr>";
		printf SAVEFILE "<td width=8%% align=left>%s</td>", ($$RUN{swingsAt}{$_}{$defender} // "");
		printf SAVEFILE "<td width=5%% align=center>%s</td>", ($$RUN{hitsEnemy}{$_}{$defender} // "");
		printf SAVEFILE "<td width=5%% align=right>%s</td>", ($$RUN{critsEnemy}{$_}{$defender} // "");
		print SAVEFILE "</tr></table></td>";


		print SAVEFILE "<td width=15%><table border=0><tr><td width=5% align=left>";
		
		if (exists($$RUN{swingsAt}{$_}{$defender}) && $$RUN{swingsAt}{$_}{$defender}>0) {
		    $$RUN{hitsEnemy}{$_}{$defender} = 0 if (!exists($$RUN{hitsEnemy}{$_}{$defender}));

		    my $ptilde = ($$RUN{hitsEnemy}{$_}{$defender}+2) / ($$RUN{swingsAt}{$_}{$defender}+4);
		    my $se = sqrt($ptilde*(1-$ptilde)/($$RUN{swingsAt}{$_}{$defender}+4));
		    print SAVEFILE int(1000*($$RUN{hitsEnemy}{$_}{$defender}/$$RUN{swingsAt}{$_}{$defender}))/10 . "%</td><td align=center width=15%>(" . int(($ptilde-1.96*$se)*1000)/10 . " - " . int(($ptilde+1.96*$se)*1000)/10 .")</td>";
		}
		else {
		    print SAVEFILE "</td><td></td>";		    
		}
		print SAVEFILE "<td align=right width=5%>";
		if (exists($$RUN{swingsAt}{$_}{$defender}) && $$RUN{swingsAt}{$_}{$defender}>0) {
		    $$RUN{missConcealed}{$_}{$defender} = 0 if (!exists($$RUN{missConcealed}{$_}{$defender}));
		    $$RUN{hitsEnemy}{$_}{$defender} = 0 if (!exists($$RUN{hitsEnemy}{$_}{$defender}));
		    if ($$RUN{swingsAt}{$_}{$defender} == $$RUN{missConcealed}{$_}{$defender}) {
			print SAVEFILE "0"
		    }
		    else {
			print SAVEFILE int(1000*$$RUN{hitsEnemy}{$_}{$defender} / ($$RUN{swingsAt}{$_}{$defender} - $$RUN{missConcealed}{$_}{$defender}))/10 . "%";
		    }
		}
		print SAVEFILE "</td>";
		print SAVEFILE "</tr></table>";


		print SAVEFILE "<td align=right>" . ($$RUN{damEnemy}{$_}{$defender} // "") . "</td></tr>"
		
	    }
	    print SAVEFILE "</table>";
	    print SAVEFILE "</font>";

	    print SAVEFILE "<p><b>Damage received:</b><p>";
	    print SAVEFILE "<font size=\"-1\">";
	    print SAVEFILE "<table width=100% border=1><tr><th width=40% bgcolor=lightgray>Name</th><th bgcolor=lightgray width=6%>Deaths by</th><th bgcolor=lightgray width=10%>Attacks by</th><th bgcolor=lightgray width=25%>Hit %</th><th bgcolor=lightgray>Total damage</th></tr>";	    
            foreach my $id (sort keys %{ $$RUN{killsEnemy} }) {
		if ( exists($$RUN{killsEnemy}{$id}{$_}) || exists($$RUN{damEnemy}{$id}{$_}) || exists($$RUN{swingsAt}{$id}{$_})) {
		    print SAVEFILE "<tr><td>$id</td><td align=right>" . ($$RUN{killsEnemy}{$id}{$_} // "") . "</td>";
		    print SAVEFILE "<td align=right>" . ($$RUN{swingsAt}{$id}{$_} // "") . "</td>";
		    printf SAVEFILE "<td align=right>%5.1f</td>", ((exists($$RUN{swingsAt}{$id}{$_}) && exists($$RUN{hitsEnemy}{$id}{$_})) ? 100*($$RUN{hitsEnemy}{$id}{$_}/$$RUN{swingsAt}{$id}{$_}) : 0);
		    print SAVEFILE "<td align=right>" . ($$RUN{damEnemy}{$id}{$_} // "") . "</td></tr>";
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


sub yal_save_inventories {
    my $file = $YW{mw}->getSaveFile(-initialfile=> 'gear.html',
				-filetypes=>[['HTML files', '.html'],
					     ['ASCII files', '.txt'],
					     ['All Files', '*']],
				-defaultextension => '.html');
    $file =~ /.*\.(.*)/;
    my $extension = $1;

    if (defined($file)) {
	open(SAVEFILE, ">$file");

	if ($extension eq "txt") {
	    foreach my $container (sort keys (%{ $YAL{gear} })) {
		print SAVEFILE "Container ($container):\n=====================\n\n";
		foreach my $item (sort keys (%{$YAL{gear}{$container}})) {
		    print SAVEFILE "  $item";
		    print SAVEFILE " x$YAL{gear}{$container}{$item}" if ($YAL{gear}{$container}{$item}>1);
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
	    foreach my $container (sort keys (%{ $YAL{gear} })) {	
		print SAVEFILE "<li> <a href=\"#$container\">$container</a>";
	    }
	    print SAVEFILE "</ul>";
	    print SAVEFILE "<hr>";
	    print SAVEFILE "<h1>Detailed listing</h1>";
	    foreach my $container (sort keys (%{ $YAL{gear} })) {		    
		print SAVEFILE "<div class=\"combatant\"><h3><a name=\"$container\">$container</a></h3>\n";
		foreach my $item (sort keys (%{$YAL{gear}{$container}})) {
		    $_ = $item;
		    s/ /_/g;
		    print SAVEFILE "<a href=\"http://www.hgwiki.com/wiki/index.php?title=$_\">$item</a>";
		    print SAVEFILE " x$YAL{gear}{$container}{$item}" if ($YAL{gear}{$container}{$item}>1);
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

######################################################################

# management of runs

sub runlog_start {
    my $fname = shift;
    $YAL{save_to_file} = $fname // $YW{mw}->getSaveFile(-initialfile=> 'lastrun.txt',
				-filetypes=>[['Text files', '.txt'],
					     ['All Files', '*']],
				-defaultextension => '.txt');
    
    if (defined($YAL{save_to_file})) {
	open(SAVEFILE, ">$YAL{save_to_file}");

	# Change the menubuttons so start run is disabled
	$YW{menu_file}->entryconfigure('End run', -state=>'normal');
	$YW{menu_file}->entryconfigure('Start a run', -state=>'disabled');

	$YAL{saverunbuffer} = "";
	$$RUN{logFirstTS} = $$RUN{srvLogTS} if $$RUN{srvLogTS}; # update timestamp for run-start

	# Initiate a timer that saves the data to the file.
	$YAL{savefiletimer} = $YW{mw}->repeat(10000 => \&runlog_save_buffer);	

	$currentRun{savefile} = $YAL{save_to_file};
    } else {
	delete $currentRun{savefile};
    }
}

sub runlog_end {
    runlog_save_buffer();
    close(SAVEFILE);
    $YW{menu_file}->entryconfigure('End run', -state=>'disabled');
    $YW{menu_file}->entryconfigure('Start a run', -state=>'normal');
    $YAL{savefiletimer}->cancel;
    undef($YAL{saverunbuffer});
    if ($OPTIONS{'autostartrun'}) {
	my $tofile = $YW{mw}->getSaveFile(
	    -title => 'Save run-log as ...',
	    -initialfile=> time2str("%Y%m%d_%H%M_", $$RUN{logFirstTS}) . ($$RUN{lastRun} || $$RUN{toon} || 'HG') . '.txt',
	    -filetypes=>[['Text files', '.txt'],
			 ['All Files', '*']],
	    -defaultextension => '.txt'
	);
	if ($tofile && ($tofile ne $YAL{save_to_file})) {
	    copy($YAL{save_to_file}, $tofile) or print "\nERROR\ncannot copy run-file\n\n";
	    #hg_run_copy($tofile);
	}
    }
    $YAL{save_to_file} = '';
}


sub runlog_save_buffer {
    print SAVEFILE $YAL{saverunbuffer};
    $YAL{saverunbuffer}="";
}

sub hg_run_init {
    %emptyRun = (
	# who is playing
	data => {},
	name => 'current',
	toon => '', # name of our current toon
	player => '', # our login-name
	toonList => {}, # toons - potential party members
	partyList => {}, # current party members
	# combat data
	damIn => 0, # damage done to party members
	damOut => 0, # damage done by party members
	deaths => 0, # nrof deaths of our toon
	kills => 0, # nrof kills of our toon
	paracount => {}, # Number of paragon hell monsters
	totalmobkills => 0, # total number of mobs killed (by party?)
	hits => 0, # our own toon hits a mob
	lastKilled => '', # last kill of our toon
	lastKiller => '', # last killer of our toon
	hit_frequency => 0,
	defence_frequency => 0,
	# where are we
	srvName => '', # server name (number) we are currently on
	srvUptime => 0, # current uptime in seconds
	srvRound => 0, # every 6 seconds a new round.
	srvLogTS => 0, # timestamp read from logfile
	srvBaseUptime => 0, # uptime read from greeting
	srvBaseTS => 0, # at which time (from log) did we catch the uptime msg
	logFirstTS => 0, # first timestamp we've seen in the log
	srvModDate => '', # date of module build
	movements => [], # waypoints
	cMap => '', # current map
	cArea => '', # current area
	lastRun => '', # which non-ignore area == run were we last in?
	# misc stuff
	totalxp => 0,
	dam_taken_detail => {}, # for immunity/vulnerability calcs
    );
}

sub hg_run_reset {
    my ($k, $v);
    while (($k, $v) = each (%currentRun)) {
	next if !$v; # value already false, nothing to reset
	if (defined($emptyRun{$k})) {
	    my $t = ref $emptyRun{$k};
	    if ($t) {
		if ($t eq 'HASH') { $currentRun{$k} = {}; }
		elsif ($t eq 'ARRAY') { $currentRun{$k} = []; }
		# TODO: else we have a scalar-ref
	    } else { # we have a scalar
		$currentRun{$k} = $emptyRun{$k};
	    }
	} else {
	    # not in blueprint - remove and shout
	    print "deleting run prop '$k'\n";
	    delete $currentRun{$k};
	}
    }
    $runData = $$RUN{data}; # run data of individual actors (mobs or party members)}
}

sub hg_run_new_actor {
    my ($name, $isPM) = @_;
    my $a = {
	# combat - outgoing
	kills => 0,
	lastKilled => '',
	damOut => 0, # outgoing damage total
	    # damOutTypes => {}, # flags for dealt damage types
	swingsOut => 0,
	hits => 0,
	crits => 0,
	# combat - incoming
	deaths => 0,
	lastKiller => '',
	damIn => 0,
	damInStr => '', # for immunity/vulnerability calcs
	swingsIn => 0,
	dodge => 0,
	# misc stuff for party members
	badToonHits => 0, # Counts the number of attacks on Mammon's tears, infernal machines etc. Purely for pointing the finger at someone
	hitPercentage => '',
	# props for data collecting
	conceal => 0,
	    #immuneTo => {},
	    #effects => {},
    };
    $$RUN{data}{$name} = $a;
    # TODO: check if $name is partymember, known mob, ... or unknown thing
    return $a;
}

#
# Function return 1 if the name is considered a party member and 0 otherwise
#
sub partymember {
    my $id = shift @_;
    return $$RUN{partyList}{$id} // 0;
    #return 1 if (exists($deaths{$id}) || $id eq $$RUN{toon});
    #return 0;
}


sub new_party_member {
    my $id = shift @_;
    # TODO: check for and do something about leading whitespace
    $$RUN{partyList}{$id} = 1;
    $$RUN{toonList}{$id} = 1;
    hg_run_new_actor($id, 1) if !$$runData{$id};
}

#
# These function grab information from the general
#
sub toon_kills {
    my $toon = shift;
    return $$runData{$toon}{kills} // 0;
}


#
# Configuration functions
#

sub configure_fonts {
    foreach my $colour (@COLS) {
	$YW{damage_out}->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]);
	$YW{damage_out}->tagConfigure($colour.'HL', -background => "$colour", foreground => 'black');
	$YW{damage_inc}->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]);
	$YW{imms}->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font"}, -size => 9]);
	$YW{dmgheader_out}->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]);
	$YW{dmgheader_inc}->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font"}, -size=>$OPTIONS{"fontsize"}]);
	$YW{hits_inc}->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font-hit"}, -size=>$OPTIONS{"fontsize-hit"}]);
	$YW{hits_out}->tagConfigure($colour, -foreground => "$colour",
				  -font=>[-family=>$OPTIONS{"font-hit"}, -size=>$OPTIONS{"fontsize-hit"}]);
	$YW{saves}->tagConfigure($colour,
				  -font=>[-family=>$OPTIONS{"font-resist"}, -size=>$OPTIONS{"fontsize-resist"}]);
	$YW{resists}->tagConfigure($colour,
				  -font=>[-family=>$OPTIONS{"font-resist"}, -size=>$OPTIONS{"fontsize-resist"}]);
	$YW{t_chatlog}->tagConfigure($colour, -foreground=>"$colour");

	$YW{top_info_area}->tagConfigure($colour, -foreground=>"$colour");
    } 
}

sub calculate_vulnerabilities {
    my(@damdet);
    my(%damnum);
    for my $detail (keys %{ $$RUN{dam_taken_detail} }) {
	my ($mob, $dtype) = split(/ :d: /, $detail);
	my $tdam = $$runData{$mob}{damIn};
	my $cdam = $$RUN{dam_taken_detail}{$detail};

	# If a mob only received 0 damage from element then possibly immune
	if ($cdam==0) {
	    $$HGmobs{$mob}{immsEl}{$dtype}=1;	    
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
	    $$runData{$mob}{damInStr} = "$pstr\% $dtype";
	} elsif ($damnum{$mob} < 4) {
	    $$runData{$mob}{damInStr} .= ", $pstr\% $dtype";
	}
    }    
}


sub parse_old_log_file {
    my $file = $YW{mw}->getOpenFile(-initialfile=> 'oldlogfile.txt',
				-filetypes=>[['Text files', '.txt'],
					     ['All Files', '*']],
				-defaultextension => '.txt');
    
    if (defined($file)) {
	# Halt the automatic parsing
	$YAL{parsetimer}->cancel;
	my $originalfile = $YAL{currentlogfile};
	my $location = tell(LOGFILE);

	$YAL{currentlogfile} = $file;
	$YAL{isCurrent} = 0;

	open (LOGFILE, $file);
	parse_log_file();
	close(LOGFILE);
	
	$YAL{currentlogfile} = $originalfile;
	$YAL{isCurrent} = ($originalfile =~ /nwclientLog\d\.txt/);

	open (LOGFILE, $YAL{currentlogfile});
	seek(LOGFILE, $location, 0);

	# Restart the original parser
	$YAL{parsetimer} = $YW{mw}->repeat($YAL{parsetime} => \&parse_log_file);
    }
}



#
# The following functions deal with saving and loading/validation of the configuration file
#

sub yal_save_config {
    open(CFGFILE, ">$YAL{cfgfile}") || die "Could not create configuration file";

    # Get the current layout
    $OPTIONS{"geometry"} = $YW{mw}->geometry();

    foreach $_ (sort keys(%OPTIONS)) {
        print CFGFILE "$_=$OPTIONS{$_}\n";	
    }
    close(CFGFILE);

    if ($OPTIONS{'autostartrun'}) {
	if (!$YAL{save_to_file} && ($YAL{currentlogfile} =~ /^nwclientLog[1-4]\.txt$/)) {
	    print "autostart run\n";
	    runlog_start('currentrun.txt');
	}
    }
}


sub yal_load_config {
    if (-e $YAL{cfgfile}) {
        open(CFGFILE, "$YAL{cfgfile}") || die "Could not open configuration file";
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
	$YW{mw}->geometry($OPTIONS{"geometry"}) if ($OPTIONS{"geometry"} ne "");
    }
}

sub gui_update_info_area {
    my ($widget, $options, $def_color) = @_;
    $widget->delete("1.0", 'end');
    my $i = 0;
    for my $opt (@{$options}) {
	$widget->insert('end', " |", $def_color) if $i++;
	if ($opt eq 'server') {
	    $widget->insert('end', " Srv $$RUN{srvName}", $def_color);
	    if ($$RUN{srvBaseUptime}) {
		$widget->insert('end', ' up '.time2str("%R", $$RUN{srvUptime}, 0), $def_color); # TODO: change color with uptime
	    }
	}
	elsif ($opt eq 'area') {
	    $widget->insert('end', " $$RUN{lastRun}:", $def_color) if $$RUN{lastRun};
	    if ($$RUN{cMap}) { # TODO: && $OPTIONS{'show_area_info'}
		$widget->insert('end', " $$RUN{cMap}", $def_color);
		if ($HGmaps->{$$RUN{cMap}}{'respawn'}) {
		    $widget->insert('end', ' '.$HGmaps->{$$RUN{cMap}}{'respawn'}, 'red');
		}
	    }
	}
    }
}

sub gui_update_top_info_area {
    gui_update_info_area($YW{top_info_area}, ['server', 'area'], '');
}

#
# some helper functions in preparation to using hgdata.xml
#
my %hgmonsters = ();
my %hg_ignore_enemies = ();

sub hg_para_level {
    my $monster = shift;
    if (exists($HGmobs->{$monster})) {
	return $HGmobs->{$monster}{'paragon'} || 0;
    }
    return 0; #exists($PARAMONSTERS{$monster}) ? $PARAMONSTERS{$monster} : 0;
}

sub hg_do_not_hit {
    my $monster = shift;
    # TODO: remove usage of "old" data once we get nohit-flags in xml-data
    return 1 if exists($DONOTHIT{$monster});
    if (exists($HGmobs->{$monster})) {
	return exists($HGmobs->{$monster}{'kb'}); # eq 'Area';
    }
    return 0;
    #return exists($DONOTHIT{$monster});
}

sub hg_ignore_enemy {
    my $monster = shift;
    return $HGmobs->{$monster}{'ignore'} // 0; #exists($hg_ignore_enemies{$monster});
}

sub hg_mob_heals {
    my $monster = shift;
    my $type = shift;
    return 0 if (!exists($HGmobs->{$monster}) || !exists($HGmobs->{$monster}{'heal'}));
    my $h = $HGmobs->{$monster}{'heal'};
    return $type ? $h->{$type} : $h;
}

sub append_monster {
    my ($widget, $monster) = @_;

    my $color = 'white';
    my $flags = '';
    my $heals = '';

    if (exists($HGmobs->{$monster})) {
	my $m = $HGmobs->{$monster};
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
		    $widget -> insert('end', $damage_type->{$_}, "$COLOURS{$_}HL");
		    $widget -> insert('end', "\t", "$COLOURS{$_}");
		} else {
		    $widget -> insert('end', $damage_type->{$_} . "\t", "$COLOURS{$_}");
		}
	    } 
	    else {
		if ($heals && $heals->{$_}) {
		    $widget -> insert('end', "-", "$COLOURS{$_}");
		}
		# TODO: elsif (mob takes dmg)
		$widget -> insert('end', "\t", "$COLOURS{$_}");
	    }
	}

	if ($eso_show eq 'sum') {
	    $widget -> insert('end', ($eso_color ? "$eso_dmg" : '')."\t", $eso_color);
	}

	append_monster($widget, $mob);
}

######################################################################
## Initialization ...

sub yal_init {
    # basic config for YAL, state vars for parsing
    %YAL = (
	cfgfile => 'yal.cfg',
	logfilenumber => 1,
	currentlogfile => 'nwclientLog1.txt',
	parsetime => 3000, # reparse log every 3 seconds
	statusmessage => '', # text for statusbar at the bottom
	bankchest => 'default',
	gearcontainer => '',
	hit_frequency_weight => 30,
	save_to_file => '', # name of file we're saving the current run to
	effectId => undef, # Id to keep information about who effect listings concern
	logfile_info => "?", # info-string about current logfile
	catchPartyWho => 0, # autofill party when we get player list of our server?
	myServerWho => 0, # are next items in !who output from our server?
	isCurrent => 1, # are we parsing direct nwn output or old logfile
	effectTimers => {}, # the key is the name of the effect the value is the duration of the effect
	effectTimersMax => {}, # stores the values from the effects command so when you cast a spell it shows up in your effects
	timerGSmite => [], # timers for greater smite
	timerGSanct => [], # timers for greater sanctuaray
    );

    # prepare structure to store HG base data in
    %HGdata = (
	mob	=> {}, # the enemies we encounter
	area	=> {}, # area (containing maps and mobs) we know about
	map	=> {},
	toon	=> {}, # base data of toons (own and party)
	new	=> {}, # remember things we didn't know about so far
    );
    # set some references for quicker access
    $HGmobs = $HGdata{'mob'};
    $HGmaps = $HGdata{'map'};
    $HGareas = $HGdata{'area'};
    $HGtoons = $HGdata{'toon'};
    $HGnew = $HGdata{'new'};

    # prepare structure to save run data in
    hg_run_init();
    %currentRun = %emptyRun;
    hg_run_reset();
}

sub hgdata_import_xml {
    my $file = 'hgdata.xml';
    my @otags = (); # open tags
    my $ctTag; # container tag ref

    open(IN, $file) || die "Can't open XML file '$file'\n";
    my $header = <IN>;
    $header =~ /^<\?xml.*\?>/ || die "Not an XML file\n";

    # read the data
    while (<IN>) {
	s/^\s*(.*?)\s*$/$1/;
	next if !$_; # line empty now
	if (/<(\/?)(\w+)\s*(.*?)\s*(\/?)>/) {
	    my ($sl1, $tagName, $atts, $sl2) = ($1, $2, $3, $4);
	    my %tag = (tag => $tagName);

	    if ($sl1) { # closing tag
		my $oTag = pop @otags;
		die "Invalid xml file - closing tag doesn't match opening tag ($oTag->{tag}/$tagName)\n" if $oTag->{'tag'} ne $tagName;
		$ctTag = $otags[-1];
		next; # closing tag has no attributes
	    }

	    # extract name if defined
	    $atts =~ s/name=\"(.*?)\"//;
	    my $cName = $1 // ''; # current name = value name attribute
	    if ($cName && exists($HGdata{$tagName}{$cName})) {
		# duplicate - probably mob in another area
		next;
	    }

	    # get rest of attributes
	    my $cObj = {}; # current object
	    while ($atts =~ s/^\s*(\w+)=\"(.*?)\"//) {
		$$cObj{$1} = $2;
	    }

	    # save object for quick access
	    if ($cName) {
		$HGdata{$tagName}{$cName} = $cObj;
		# and put a ref in container (if we have a named container)
		$ctTag->{'obj'}{$tagName}{$cName} = $cObj if $ctTag && $ctTag->{'obj'};
	    }

	    if ($tagName eq 'map') {
		$$cObj{'area'} = $ctTag->{'name'}; # container is area, take name of container
	    }
	    elsif ($tagName eq 'mob') {
		if (exists($$cObj{'race'})) {
		    $$cObj{'race'} =~ /^(\w)(\w)\w+( (\w)\w+)?$/;
		    $$cObj{'race_short'} = $1 . (defined($4) ? $4 : $2);
		}
		if (exists($$cObj{'type'})) {
		    $$cObj{'type'} =~ /^(\w)\w+( (\d))?$/;
		    $$cObj{'type_short'} = $1;
		    $$cObj{'type_short'} .= $3 if defined($3);
		}
		if (exists($$cObj{'qual'}) && ($$cObj{'qual'} =~ /^(\d)\.0$/)) {
		    $$cObj{'qual'} = $1; # strip ".0" from end of qual if it's there
		}
		if (exists($$cObj{'heals'})) {
		    my ($el, $proc) = split(/ /, $$cObj{'heals'});
		    $$cObj{'heal'}{$el} = $proc;
		}
		if (exists($$cObj{'syn'})) { # build translation hash if we have a syn-attribute
		    $HGdata{'syn'}{$$cObj{'syn'}} = $cName;
		}
	    }

	    if (!$sl2) { # opening tag
		die "Not a HG xml file\n" if ($#otags < 0) && ($tagName ne 'hg');
		if (($tagName eq 'version') && /<number>(.*)<\/number>/) {
		    $HGdata{'version'} = $1;
		    next;
		}
		$tag{'name'} = $cName if $cName;
		$tag{'obj'} = $cObj;
		push @otags, \%tag;
		$ctTag = \%tag; # set container for processing children
	    }
	    # else: simple tag with no children
	}
    }

    # do some post-processing
    my ($name, $obj);
    while (($name, $obj) = each %{$HGdata{'ignore'}}) {
	#print "moving ignored mob: $name\n";
	$HGdata{'mob'}{$name} = $obj;
	$HGdata{'mob'}{$name}{'ignore'} = 1;
    }
    #delete $HGdata{'ignore'};

}
