(* ::Package:: *)

BeginPackage["Shamsi`"]
(*
Shamsi Calendar for Wolfram Language

by Pooria Soltani

Notes:
------
* The functions defined here rely on the built-in Wolfram Language
  functions,so they can't be ported to other languages easily.
* Shamsi leap year test ("ShLeapYearQ") is done according to Wikipedia:
  https://goo.gl/x3lYZh
* The origin Shamsi date is 1300/01/01,the corresponding Gregorian date
  is 1921/03/21
* The conversion functions are tested for the range 1300/01/01 to
  1469/12/29 (or 1921/03/21 to 2091/03/19).
  The test was carried out using the fof-1 rule (since "ToGregorian"
  is the inverse function of "ToGregorian"). The result was the same
  as the following:
  DateRange[{1921,3,21},{2091,3,19}]

2Do:
----
1. The functions though working accuratly, are slow and need to be
   optimized!
2. The functions should be converted to a package.

The algorithm:
--------------
Shamsi\[Rule]Gregorian:
1. Calculate the number of days since the origin (1300/01/01)
2. Use the "DatePlus" function to obtain the date with the calculated
   difference

Gregorian\[Rule]Shamsi:
1. Calculate the number of days since the origin (1921/03/21)
2. Find the respective Shamsi date using the defined "ShDatePlus"
   function
*)

ShLeapYearQ::usage="ShLeapYearQ[year] returns True if year is a leap year, "<>
	"and False if otherwise. Note: 1300\[LessEqual]y\[LessEqual]1469.";

ShDaysSince::usage="ShDaysSince[year,month,day] returns the number of "<>
	"days passed since the defined Shamsi calendar origin, 1300/01/01. "<>
	"Note: 1300\[LessEqual]y\[LessEqual]1469.";

ShDatePlus::usage="ShDatePlus[days] returns the Shamsi date, days after "<>
	"the defined Shamsi calendar origin, 1300/01/01. Note: 0\[LessEqual]days\[LessEqual]62091.";

ToGregorian::usage="ToGregorian[year,month,day] returns the corresponding "<>
	"Gregorian date of the Shamsi date year/month/day";

ToShamsi::usage="ToShamsi[year,month,day] returns the corresponding "<>
	"Shamsi date of the Gregorian date year/month/day";
	
ShDayName::usage="ShDayName[day] returns the name of the weekday.";

ShMonthName::usage="ShMonthName[month] returns the name of the month."

ShHolidayQ::usage="ShHolidayQ[year,month,day] returns True if the date "<>
	"year/month/day is an official Shamsi holiday and False otherwise."

ShHolidayName::usage="ShHolidayName[year,month,day] returns a list "<>
	"containing the event(s) of the date year/month/day if it's an "<>
	"official Shamsi holiday and None otherwise."

ShBusinessDayQ::usage="ShBusinessDayQ[year,month,day] returns True if "<>
	"the date year/month/day is a business day and False otherwise. "<>
	"Note that: ShBusinessDayQ=Not[ShHolidayQ]."

ShDateRange::usage="ShDateRange[date1,date2,increment] returns a list "<>
	"of dates beginning from date1 and ending in date2 with the "<>
	"specified increment."

ShDateAfter::usage="ShDateAfter[date,n] returns the date n day after "<>
	"the specified date."

Shamsi::usage="Returns the current date in Shamsi calendar."

ShToday::usage="Returns the current date in Shamsi calendar."

ShTomorrow::usage="Returns Tomorrow's date in Shamsi calendar."

ShYesterday::usage="Returns Yesterday's date in Shamsi calendar."


Begin["`Private`"]


(* Variables: *)

(* The "leapYears" list is calculated via the ShLeapYearQ function *)
leapYears={
1300,1304,1309,1313,1317,1321,1325,1329,1333,1337,
1342,1346,1350,1354,1358,1362,1366,1371,1375,1379,
1383,1387,1391,1395,1399,1404,1408,1412,1416,1420,
1424,1428,1432,1437,1441,1445,1449,1453,1457,1461,
1465
};

ShDays={
"Shanbe","Yekshanbe","Doshanbe","Seshanbe",
"Chahrshanbe","Panjshanbe","Jome'e"
};

ShDaysFarsi={
"\:0634\:0646\:0628\:0647","\:06cc\:06a9\:0634\:0646\:0628\:0647","\:062f\:0648\:0634\:0646\:0628\:0647","\:0633\:0647\:200c\:0634\:0646\:0628\:0647",
"\:0686\:0647\:0627\:0631\:0634\:0646\:0628\:0647","\:067e\:0646\:062c\:0634\:0646\:0628\:0647","\:062c\:0645\:0639\:0647"
};

GrDays={
"Saturday","Sunday","Monday","Tuesday",
"Wednesday","Thursday","Friday"
};

ShMonths={
"Farvardin","Ordibehesht","Khordad",
"Tir","Mordad","Shahrivar",
"Mehr","Aban","Azar",
"Dey","Bahman","Esfand"
};

ShMonthsFarsi={
"\:0641\:0631\:0648\:0631\:062f\:06cc\:0646","\:0627\:0631\:062f\:06cc\:0628\:0647\:0634\:062a","\:062e\:0631\:062f\:0627\:062f",
"\:062a\:06cc\:0631","\:0645\:0631\:062f\:0627\:062f","\:0634\:0647\:0631\:06cc\:0648\:0631",
"\:0645\:0647\:0631","\:0622\:0628\:0627\:0646","\:0622\:0630\:0631",
"\:062f\:06cc","\:0628\:0647\:0645\:0646","\:0627\:0633\:0641\:0646\:062f"
};

(* In the next 2 associations, the main keys represent months of the
year and in each month, the subkeys denote the events. Events might
be holidays, or not. For the time being, only holidays are added. *)
shamsiHolidays=<|
	1-><|
		1-><|"holiday"->True,"event"->{"\:062c\:0634\:0646 \:0646\:0648\:0631\:0648\:0632 (\:062c\:0634\:0646 \:0633\:0627\:0644 \:0646\:0648)"}|>,
		2-><|"holiday"->True,"event"->{"\:0639\:06cc\:062f\:0646\:0648\:0631\:0648\:0632"}|>,
		3-><|"holiday"->True,"event"->{"\:0639\:06cc\:062f\:0646\:0648\:0631\:0648\:0632"}|>,
		4-><|"holiday"->True,"event"->{"\:0639\:06cc\:062f\:0646\:0648\:0631\:0648\:0632"}|>,
		12-><|"holiday"->True,"event"->{"\:0631\:0648\:0632 \:062c\:0645\:0647\:0648\:0631\:06cc \:0627\:0633\:0644\:0627\:0645\:06cc \:0627\:06cc\:0631\:0627\:0646"}|>,
		13-><|"holiday"->True,"event"->{"\:062c\:0634\:0646 \:0633\:06cc\:0632\:062f\:0647 \:0628\:0647 \:062f\:0631"}|>|>,
	2-><||>,
	3-><|
		14-><|"holiday"->True,"event"->{"\:0631\:062d\:0644\:062a \:062d\:0636\:0631\:062a \:0627\:0645\:0627\:0645 \:062e\:0645\:06cc\:0646\:06cc"}|>,
		15-><|"holiday"->True,"event"->{"\:0642\:06cc\:0627\:0645 15 \:062e\:0631\:062f\:0627\:062f"}|>|>,
	4-><||>,5-><||>,6-><||>,7-><||>,8-><||>,9-><||>,10-><||>,
	11-><|
		22-><|"holiday"->True,"event"->{"\:067e\:06cc\:0631\:0648\:0632\:06cc \:0627\:0646\:0642\:0644\:0627\:0628 \:0627\:0633\:0644\:0627\:0645\:06cc"}|>|>,
	12-><|
		29-><|"holiday"->True,"event"->{"\:0631\:0648\:0632 \:0645\:0644\:06cc \:0634\:062f\:0646 \:0635\:0646\:0639\:062a \:0646\:0641\:062a \:0627\:06cc\:0631\:0627\:0646"}|>,
		30-><|"holiday"->True,"event"->{"\:0622\:062e\:0631\:06cc\:0646 \:0631\:0648\:0632 \:0633\:0627\:0644"}|>|>
|>;
		
islamicHolidays=<|
	1-><|
		9-><|"holiday"->True,"event"->{"\:062a\:0627\:0633\:0648\:0639\:0627\:06cc \:062d\:0633\:06cc\:0646\:06cc"}|>,
		10-><|"holiday"->True,"event"->{"\:0639\:0627\:0634\:0648\:0631\:0627\:06cc \:062d\:0633\:06cc\:0646\:06cc"}|>|>,
	2-><|
		20-><|"holiday"->True,"event"->{"\:0627\:0631\:0628\:0639\:06cc\:0646 \:062d\:0633\:06cc\:0646\:06cc"}|>,
		28-><|"holiday"->True,"event"->{"\:0631\:062d\:0644\:062a \:0631\:0633\:0648\:0644 \:0627\:06a9\:0631\:0645 (\:0635)",
			"\:0634\:0647\:0627\:062f\:062a \:0627\:0645\:0627\:0645 \:062d\:0633\:0646 \:0645\:062c\:062a\:0628\:06cc (\:0639)"}|>,
		30-><|"holiday"->True,"event"->{"\:0634\:0647\:0627\:062f\:062a \:0627\:0645\:0627\:0645 \:0631\:0636\:0627 (\:0639)"}|>|>,
	3-><|
		8-><|"holiday"->True,"event"->{"\:0634\:0647\:0627\:062f\:062a \:0627\:0645\:0627\:0645 \:062d\:0633\:0646 \:0639\:0633\:06a9\:0631\:06cc (\:0639)"}|>,
		17-><|"holiday"->True,"event"->{"\:0645\:06cc\:0644\:0627\:062f \:0631\:0633\:0648\:0644 \:0627\:06a9\:0631\:0645 (\:0635)",
			"\:0645\:06cc\:0644\:0627\:062f \:0627\:0645\:0627\:0645 \:062c\:0639\:0641\:0631 \:0635\:0627\:062f\:0642 (\:0639)"}|>|>,
	4-><||>,5-><||>,
	6-><|
		3-><|"holiday"->True,"event"->{"\:0634\:0647\:0627\:062f\:062a \:062d\:0636\:0631\:062a \:0641\:0627\:0637\:0645\:0647 \:0632\:0647\:0631\:0627 (\:0633)"}|>|>,
	7-><|
		13-><|"holiday"->True,"event"->{"\:0648\:0644\:0627\:062f\:062a \:0627\:0645\:0627\:0645 \:0639\:0644\:06cc (\:0639)",
			"\:0631\:0648\:0632 \:067e\:062f\:0631"}|>,
		27-><|"holiday"->True,"event"->{"\:0645\:0628\:0639\:062b \:0631\:0633\:0648\:0644 \:0627\:06a9\:0631\:0645 (\:0635)"}|>|>,
	8-><|
		15-><|"holiday"->True,
		"event"->{"\:0648\:0644\:0627\:062f\:062a \:062d\:0636\:0631\:062a \:0642\:0627\:0626\:0645 (\:0639\:062c) (\:062c\:0634\:0646 \:0646\:06cc\:0645\:0647 \:0634\:0639\:0628\:0627\:0646)"}|>|>,
	9-><|
		21-><|"holiday"->True,"event"->{"\:0634\:0647\:0627\:062f\:062a \:062d\:0636\:0631\:062a \:0639\:0644\:06cc (\:0639)"}|>|>,
	10-><|
		1-><|"holiday"->True,"event"->{"\:0639\:06cc\:062f \:0633\:0639\:06cc\:062f \:0641\:0637\:0631"}|>,
		2-><|"holiday"->True,"event"->{"\:062a\:0639\:0637\:06cc\:0644 \:0628\:0647 \:0645\:0646\:0627\:0633\:0628\:062a \:0639\:06cc\:062f \:0633\:0639\:06cc\:062f \:0641\:0637\:0631"}|>,
		25-><|"holiday"->True,"event"->{"\:0634\:0647\:0627\:062f\:062a \:0627\:0645\:0627\:0645 \:062c\:0639\:0641\:0631 \:0635\:0627\:062f\:0642 (\:0639)"}|>|>,
	11-><||>,
	12-><|
		10-><|"holiday"->True,"event"->{"\:0639\:06cc\:062f \:0633\:0639\:06cc\:062f \:0642\:0631\:0628\:0627\:0646"}|>,
	18-><|"holiday"->True,"event"->{"\:0639\:06cc\:062f \:0633\:0639\:06cc\:062f \:063a\:062f\:06cc\:0631 \:062e\:0645"}|>|>
|>;


ShLeapYearQ[year_Integer/;1300<=year<=1469(* Range from Wikipedia *)]:=
	With[
		{rem1={1,5,9,13,17,22,26,30},
		rem2={1,5,9,13,18,22,26,30}},
		If[
			year<=1342,
			MemberQ[rem1,Mod[year,33]],
			MemberQ[rem2,Mod[year,33]]
		]
	]
SetAttributes[ShLeapYearQ,Listable];

ShLeapYearQ[]:=
	ShLeapYearQ[ToShamsi[][[1]]]


ShDaysSince[y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,
	d_Integer/;1<=d<=31]:=
	(* After the year 1469, the function is inaccurate by at least 1 day *)
	If[
		m<7,
		
		Length[Select[leapYears,#<=y-1&]]+365*(y-1300)+31*(m-1)+d-1,
		
		Length[Select[leapYears,#<=y-1&]]+365*(y-1300)+31*6+30*(m-6-1)+d-1
	]

ShDaysSince[{y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,
	d_Integer/;1<=d<=31}]:=
	ShDaysSince[y,m,d]

ShDaysSince[
		{y1_Integer/;1300<=y1<=1469,m1_Integer/;1<=m1<=12,
		d1_Integer/;1<=d1<=31},
		{y2_Integer/;1300<=y2<=1469,m2_Integer/;1<=m2<=12,
		d2_Integer/;1<=d2<=31}]:=
		ShDaysSince[y2,m2,d2]-ShDaysSince[y1,m1,d1]

ShDaysSince[]:=
	ShDaysSince[ToShamsi[]]


ShDatePlus[days_Integer/;0<=days<=62091]:=
	(* Dates before 1300/01/01 won't be considered *)
	Block[
		{rem=days,y=1300,m=1,d=1},
		(*
		This function calculates the Shamsi date by counting the days
		of each year,until there are no days left, "rem" stands for
		the remaining days.
	
		The shamsi year 1300 is a leap year!
	
		If rem\[Equal]0,then the default values are correct (1300/01/01).
		*)
		While[
			0<rem,
			Which[
				rem<365,
				(* Checking if the remaining days make up a whole year *)
					If[
						rem<=6*31,
						(* Checking if the remaining days make up a 
						half-year *)
						
						m+=Floor[rem/31];
						d+=Mod[rem,31];
						rem-=(m-1)*31+d,
					
						rem-=6*31;
						m+=Floor[rem/30]+6;
						d+=Mod[rem,30];
						rem-=(m-1)*31+d
					],
				
				rem==365,
					If[
						MemberQ[leapYears,y],
						(* In a leap year, 365 days after the 1st day is
						the last day of thay year, or "year/12/30" *)
						
						m=12;d=30;rem-=365,
						
						y+=1;rem-=365
					],
				
				365<rem,
					If[
						MemberQ[leapYears,y],
						y+=1;rem-=366,
						y+=1;rem-=365
					]
			]
		];
		{y,m,d}
	]
SetAttributes[ShDatePlus,Listable];


ToGregorian[y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,d_Integer/;1<=d<=31,
	obj:(0|1):0]:=
	(* The date "1921/03/21" is the respective date of Shamsi "1300/01/01". *)
	If[
		obj==0,
	
		DatePlus[{1921,3,21},ShDaysSince[y,m,d]],
	
		DateObject[DatePlus[{1921,3,21},ShDaysSince[y,m,d]]]
	]/;Not[ShLeapYearQ[y]==False&&m==12&&(d==30||d==31)]

ToGregorian[{y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,
	d_Integer/;1<=d<=31},obj:(0|1):0]:=
	ToGregorian[y,m,d,obj]


ToShamsi[y_Integer/;1921<=y<=2091,m_Integer/;1<=m<=12,d_Integer/;1<=d<=31]:=
	(* The date "1921/03/21" is the respective date of Shamsi "1300/01/01". *)
	ShDatePlus[QuantityMagnitude[DateDifference[{1921,3,21},{y,m,d}]]]

ToShamsi[{y_Integer/;1921<=y<=2091,m_Integer/;1<=m<=12,
	d_Integer/;1<=d<=31}]:=
	ToShamsi[y,m,d]

ToShamsi[obj_DateObject]:=
	Block[
		{y,m,d},
		{y,m,d}=obj[[1,1;;3]];
		ToShamsi[y,m,d]
	]

ToShamsi[]:=
	ToShamsi[Now]


ShDayName[d_String,lang:("Farsi"|"English"):"English"]:=
	If[
		MemberQ[GrDays,d],
		
		If[
			lang=="English",
			
			ShDays[[Position[GrDays,d][[1,1]]]],
			
			ShDaysFarsi[[Position[GrDays,d][[1,1]]]]
		]
	]

ShDayName[d_Symbol,lang:("Farsi"|"English"):"English"]:=
	ShDayName[ToString[d],lang]

ShDayName[d_Integer/;1<=d<=7,lang:("Farsi"|"English"):"English"]:=
	If[
		lang=="",
		
		ShDays[[d]],
		
		ShDaysFarsi[[d]]
	]

ShDayName[y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,
	d_Integer/;1<=d<=31,lang:("Farsi"|"English"):"English"]:=
	ShDayName[DayName[ToGregorian[y,m,d]],lang]

ShDayName[{y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,
	d_Integer/;1<=d<=31},lang:("Farsi"|"English"):"English"]:=
	ShDayName[y,m,d,lang]

ShDayName[date_DateObject,lang:("Farsi"|"English"):"English"]:=
	ShDayName[DayName[date],lang]

ShDayName[]:=
	ShDayName[DayName[Now]]


ShMonthName[m_Integer/;1<=m<=12,lang:("Farsi"|"English"):"English"]:=
	If[
		lang=="English",
		
		ShMonths[[m]],
		
		ShMonthsFarsi[[m]]
	]

ShMonthName[y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,
	d_Integer/;1<=d<=31,lang:("Farsi"|"English"):"English"]:=
	ShMonthName[m,lang]

ShMonthName[{y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,
	d_Integer/;1<=d<=31},lang:("Farsi"|"English"):"English"]:=
	ShMonthName[m,lang]

ShMonthName[date_DateObject,lang:("Farsi"|"English"):"English"]:=
	ShMonthName[ToShamsi[date],lang]

ShMonthName[]:=
	ShMonthName[ToShamsi[]]


ShHolidayQ[y_Integer,m_Integer,d_Integer]:=
	Block[
		{holiday,obj,islamicMonth,islamicDay},
		
		holiday=False;
		
		obj=DateObject[ToGregorian[{y,m,d}]];
		{islamicMonth,islamicDay}=CalendarConvert[obj,"Islamic"][[1,2;;3]];
		
		(* Checking for Friday *)
		Which[
			DayName[obj]==Friday,
				holiday=True,
			
			MemberQ[Keys[shamsiHolidays[m]],d],
				holiday=True,
			
			MemberQ[Keys[islamicHolidays[islamicMonth]],islamicDay],
				holiday=True
		];
		
		holiday
	]

ShHolidayQ[{y_Integer,m_Integer,d_Integer}]:=
	ShHolidayQ[y,m,d]

ShHolidayQ[date_DateObject]:=
	ShHolidayQ[ToShamsi[date]]

ShHolidayQ[]:=
	ShHolidayQ[ToShamsi[]]


ShHolidayName[y_Integer,m_Integer,d_Integer]:=
	Block[
		{holiday,event,obj,islamicMonth,islamicDay},
		
		holiday=False;
		event={};
		
		obj=DateObject[ToGregorian[{y,m,d}]];
		{islamicMonth,islamicDay}=CalendarConvert[obj,"Islamic"][[1,2;;3]];
		
		(* Checking for Friday *)
		If[
			DayName[obj]==Friday,
			
			holiday=True;
			AppendTo[event,"\:062c\:0645\:0639\:0647"]
		];
		
		(* Checking for Shamsi events *)
		If[
			KeyExistsQ[shamsiHolidays[m],d],
			
			event=Flatten[
				Append[
					event,
					shamsiHolidays[m,d,"event"]
				]
			]
		];
		
		(* Checking for Islamic events *)
		If[
			KeyExistsQ[islamicHolidays[islamicMonth],islamicDay],
			
			event=Flatten[
				Append[
					event,
					islamicHolidays[islamicMonth,islamicDay,"event"]
				]
			]
		];
		
		If[
			event=={},
			
			event=None
		];
		event
	]

ShHolidayName[{y_Integer,m_Integer,d_Integer}]:=
	ShHolidayName[y,m,d]

ShHolidayName[date_DateObject]:=
	ShHolidayName[ToShamsi[date]]

ShHolidayName[]:=
	ShHolidayName[ToShamsi[]]


ShBusinessDayQ[y_Integer,m_Integer,d_Integer]:=
	Not[ShHolidayQ[y,m,d]]

ShBusinessDayQ[{y_Integer,m_Integer,d_Integer}]:=
	ShBusinessDayQ[y,m,d]

ShBusinessDayQ[date_DateObject]:=
	ShBusinessDayQ[ToShamsi[date]]

ShBusinessDayQ[]:=
	ShBusinessDayQ[ToShamsi[]]


ShDateRange[shDate1_List,shDate2_List,increment_Integer:1]:=
	Map[
		ToShamsi[#]&,
		DateRange[
			ToGregorian[shDate1,1],
			ToGregorian[shDate2,1],
			increment
		]
	]

ShDateRange[date1_DateObject,date2_DateObject,increment_Integer:1]:=
	Map[
		ToShamsi[#]&,
		DateRange[
			date1,
			date2,
			increment
		]
	]


ShDateAfter[date_List,n_Integer]:=
	ToShamsi[DatePlus[ToGregorian[date,1],n]]

ShDateAfter[date_DateObject,n_Integer]:=
	ToShamsi[DatePlus[date,n]]

ShDateAfter[n_Integer]:=
	ToShamsi[DatePlus[Now,n]]


Shamsi:=
	ToShamsi[]


ShToday:=
	ToShamsi[]


ShTomorrow:=
	ToShamsi[Tomorrow]


ShYesterday:=
	ToShamsi[Yesterday]


End[]


EndPackage[]
