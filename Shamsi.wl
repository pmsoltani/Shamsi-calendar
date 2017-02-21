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

	ShLeapYearQ::usage="ShLeapYearQ[year] returns True if year is a leap year,
		and False if otherwise. Note: 1300\[LessEqual]y\[LessEqual]1469.";

	ShDaysSince::usage="ShDaysSince[year,month,day] returns the number of days passed
		since the defined Shamsi calendar origin, 1300/01/01. Note: 1300\[LessEqual]y\[LessEqual]1469."

	ShDatePlus::usage="ShDatePlus[days] returns the Shamsi date, days after the defined
		Shamsi calendar origin, 1300/01/01. Note: 0\[LessEqual]days\[LessEqual]62091."

	ToGregorian::usage="ToGregorian[year,month,day] returns the corresponding
		Gregorian date of the Shamsi date year/month/day"

	ToShamsi::usage="ToShamsi[year,month,day] returns the corresponding Shamsi date
		of the Gregorian date year/month/day"



Begin["`Private`"]

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

	ShDaysSince[y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,d_Integer/;1<=d<=31]:=
		(* After the year 1469, the function is inaccurate by at least 1 day *)
		With[
			{leaps={1300,1304,1309,1313,1317,1321,1325,1329,1333,
			1337,1342,1346,1350,1354,1358,1362,1366,1371,1375,1379,
			1383,1387,1391,1395,1399,1404,1408,1412,1416,1420,1424,
			1428,1432,1437,1441,1445,1449,1453,1457,1461,1465}},
			If[
				m<7,
				Length[Select[leaps,#<=y-1&]]+365*(y-1300)+31*(m-1)+d-1,
				Length[Select[leaps,#<=y-1&]]+365*(y-1300)+31*6+30*(m-6-1)+d-1
			]
		]

	ShDaysSince[{y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,d_Integer/;1<=d<=31}]:=
		ShDaysSince[y,m,d]

	ShDaysSince[
		{y1_Integer/;1300<=y1<=1469,m1_Integer/;1<=m1<=12,d1_Integer/;1<=d1<=31},
		{y2_Integer/;1300<=y2<=1469,m2_Integer/;1<=m2<=12,d2_Integer/;1<=d2<=31}]:=
		ShDaysSince[y2,m2,d2]-ShDaysSince[y1,m1,d1]
		
	ShDatePlus[days_Integer/;0<=days<=62091]:=
		(* Dates before 1300/01/01 won't be considered *)
		Module[
			{rem=days,y=1300,m=1,d=1,
			leaps={1300,1304,1309,1313,1317,1321,1325,1329,1333,
			1337,1342,1346,1350,1354,1358,1362,1366,1371,1375,1379,
			1383,1387,1391,1395,1399,1404,1408,1412,1416,1420,1424,
			1428,1432,1437,1441,1445,1449,1453,1457,1461,1465}},
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
					rem<365,(* Checking if the remaining days make up a whole year *)
					If[
						rem<=6*31,(* Checking if the remaining days make up half a year *)
						m+=Floor[rem/31];d+=Mod[rem,31];rem-=(m-1)*31+d,
						rem-=6*31;m+=Floor[rem/30]+6;d+=Mod[rem,30];rem-=(m-1)*31+d
					],
					rem==365,
					If[
						MemberQ[leaps,y], (* In a leap year, 365 days after
							the 1st day is the last day of thay year, or
							"year/12/30" *)
						m=12;d=30;rem-=365,
						y+=1;rem-=365
					],
					365<rem,
					If[
						MemberQ[leaps,y],
						y+=1;rem-=366,
						y+=1;rem-=365
					]
				]
			];
			{y,m,d}
		]
	SetAttributes[ShDatePlus,Listable];

	ToGregorian[y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,d_Integer/;1<=d<=31]:=
		(* The date "1921/03/21" is the respective date of Shamsi "1300/01/01". *)
		DatePlus[{1921,3,21},ShDaysSince[y,m,d]]

	ToGregorian[{y_Integer/;1300<=y<=1469,m_Integer/;1<=m<=12,d_Integer/;1<=d<=31}]:=
		ToGregorian[y,m,d]

	ToShamsi[y_Integer/;1921<=y<=2091,m_Integer/;1<=m<=12,d_Integer/;1<=d<=31]:=
		(* The date "1921/03/21" is the respective date of Shamsi "1300/01/01". *)
		ShDatePlus[QuantityMagnitude[DateDifference[{1921,3,21},{y,m,d}]]]

	ToShamsi[{y_Integer/;1921<=y<=2091,m_Integer/;1<=m<=12,d_Integer/;1<=d<=31}]:=
		ToShamsi[y,m,d]

End[]



EndPackage[]
