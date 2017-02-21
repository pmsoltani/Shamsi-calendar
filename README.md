# Shamsi-calendar
Shamsi calendar for the Wolfram Language

## Description
This package provides functions to convert Shamsi to/from Gregorian date. The applicable range is: 1300/01/01 to 1469/12/29 (or 1921/03/21 to 2091/03/19).

## Installation
1. Download the latest release.
2. Copy the file “Shamsi.wl” to one of the folders obtained by evaluating the following command in Mathematica:
	 `FileNameJoin[{$UserBaseDirectory,"Applications"}]`
3. Use the command `Needs["Shamsi`"]` to load the package.

For 1-time uses, you can first Import the “Shamsi.wl” file and then use the `Needs` command to load the package.

## Compatibility
The package uses the built-in functions `DatePlus` and `DateDifference` which were both introduced in Mathematica v6 and were updated in v10.

The package itself is developed using Mathematica v11 on macOS.

## Contributions
Any thoughts, suggestions, contributions are welcome. The functions need to be optimized for speed & error checking. Additional options and messages are also important.
