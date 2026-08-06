import FourColorTheorem.FourColor.Configuration.Encoding

set_option maxRecDepth 10000

/-!
The 633 reducible configuration descriptors from Gonthier's
`configurations.v`, mechanically translated to `Config.parse`.

The concrete Coq syntax treats leading rotations as contract-reference
indices rather than construction steps; `Config.parse` implements the
same convention.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Config

def cf001 : Config :=
  parse true []
[
    CpStep.rotate 13, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf002 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y
  ]

def cf003 : Config :=
  parse true []
[
    CpStep.rotate 17, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf004 : Config :=
  parse true []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 12, CpStep.rotate 13, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf005 : Config :=
  parse true []
[
    CpStep.rotate 10, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf006 : Config :=
  parse false []
[
    CpStep.rotate 19, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y
  ]

def cf007 : Config :=
  parse true []
[
    CpStep.rotate 17, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf008 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf009 : Config :=
  parse true []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y
  ]

def cf010 : Config :=
  parse false []
[
    CpStep.rotate 20, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf011 : Config :=
  parse true []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 8, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf012 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf013 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf014 : Config :=
  parse true []
[
    CpStep.rotate 14, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf015 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 9, CpStep.rotate 15, CpStep.rotate 16, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf016 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf017 : Config :=
  parse true []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf018 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf019 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf020 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 8, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf021 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf022 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf023 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 8, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf024 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf025 : Config :=
  parse true []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf026 : Config :=
  parse false []
[
    CpStep.rotate 19, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf027 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf028 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf029 : Config :=
  parse true []
[
    CpStep.rotate 4, CpStep.rotate 5, CpStep.rotate 21, CpStep.rotate 25, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf030 : Config :=
  parse false []
[
    CpStep.rotate 19, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf031 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf032 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf033 : Config :=
  parse false []
[
    CpStep.rotate 24, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf034 : Config :=
  parse false []
[
    CpStep.rotate 15, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf035 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y
  ]

def cf036 : Config :=
  parse true []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf037 : Config :=
  parse true []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf038 : Config :=
  parse false []
[
    CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf039 : Config :=
  parse true []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 8, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf040 : Config :=
  parse false []
[
    CpStep.rotate 11, CpStep.rotate 12, CpStep.rotate 21, CpStep.rotate 26, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf041 : Config :=
  parse false []
[
    CpStep.rotate 20, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf042 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf043 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf044 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf045 : Config :=
  parse true []
[
    CpStep.rotate 24, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf046 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf047 : Config :=
  parse true []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf048 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf049 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf050 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf051 : Config :=
  parse false []
[
    CpStep.rotate 14, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf052 : Config :=
  parse false []
[
    CpStep.rotate 24, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf053 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf054 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf055 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf056 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf057 : Config :=
  parse false []
[
    CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf058 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf059 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf060 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf061 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf062 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 9, CpStep.rotate 15, CpStep.rotate 16, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y
  ]

def cf063 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf064 : Config :=
  parse false []
[
    CpStep.rotate 4, CpStep.rotate 5, CpStep.rotate 22, CpStep.rotate 27, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf065 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf066 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 8, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf067 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf068 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf069 : Config :=
  parse true []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf070 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf071 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf072 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf073 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf074 : Config :=
  parse false []
[
    CpStep.rotate 15, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf075 : Config :=
  parse false []
[
    CpStep.rotate 15, CpStep.rotate 29, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf076 : Config :=
  parse true []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf077 : Config :=
  parse true []
[
    CpStep.rotate 14, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf078 : Config :=
  parse false []
[
    CpStep.rotate 14, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf079 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y
  ]

def cf080 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf081 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf082 : Config :=
  parse false []
[
    CpStep.rotate 14, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf083 : Config :=
  parse false []
[
    CpStep.rotate 4, CpStep.rotate 5, CpStep.rotate 25, CpStep.rotate 30, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf084 : Config :=
  parse false []
[
    CpStep.rotate 20, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf085 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf086 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf087 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf088 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y
  ]

def cf089 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 9, CpStep.rotate 15, CpStep.rotate 16, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf090 : Config :=
  parse true []
[
    CpStep.rotate 14, CpStep.rotate 15, CpStep.rotate 21, CpStep.rotate 22, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf091 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf092 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf093 : Config :=
  parse false []
[
    CpStep.rotate 22, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf094 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf095 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf096 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y
  ]

def cf097 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf098 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf099 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf100 : Config :=
  parse true []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf101 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf102 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf103 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y, CpStep.y
  ]

def cf104 : Config :=
  parse true []
[
    CpStep.rotate 31, CpStep.rotate 33, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf105 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y
  ]

def cf106 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf107 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf108 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf109 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y
  ]

def cf110 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf111 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf112 : Config :=
  parse true []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf113 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf114 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf115 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf116 : Config :=
  parse true []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 19, CpStep.rotate 24, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y
  ]

def cf117 : Config :=
  parse false []
[
    CpStep.rotate 14, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf118 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf119 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf120 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf121 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf122 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf123 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf124 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.rotate 13, CpStep.rotate 28, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf125 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf126 : Config :=
  parse false []
[
    CpStep.rotate 13, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf127 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf128 : Config :=
  parse false []
[
    CpStep.rotate 4, CpStep.rotate 5, CpStep.rotate 18, CpStep.rotate 23, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf129 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y
  ]

def cf130 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf131 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf132 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf133 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf134 : Config :=
  parse false []
[
    CpStep.rotate 19, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf135 : Config :=
  parse true []
[
    CpStep.rotate 13, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf136 : Config :=
  parse false []
[
    CpStep.rotate 14, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf137 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf138 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.rotate 19, CpStep.rotate 29, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf139 : Config :=
  parse false []
[
    CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf140 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.rotate 13, CpStep.rotate 29, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf141 : Config :=
  parse true []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf142 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf143 : Config :=
  parse false []
[
    CpStep.rotate 17, CpStep.rotate 22, CpStep.rotate 23, CpStep.rotate 28, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf144 : Config :=
  parse false []
[
    CpStep.rotate 14, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf145 : Config :=
  parse false []
[
    CpStep.rotate 5, CpStep.rotate 19, CpStep.rotate 27, CpStep.rotate 29, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf146 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf147 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf148 : Config :=
  parse false []
[
    CpStep.rotate 13, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf149 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf150 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf151 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y
  ]

def cf152 : Config :=
  parse false []
[
    CpStep.rotate 4, CpStep.rotate 5, CpStep.rotate 22, CpStep.rotate 27, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf153 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf154 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf155 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf156 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf157 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf158 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf159 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 32, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf160 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf161 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf162 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf163 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf164 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf165 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf166 : Config :=
  parse false []
[
    CpStep.rotate 11, CpStep.rotate 12, CpStep.rotate 18, CpStep.rotate 19, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf167 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf168 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf169 : Config :=
  parse true []
[
    CpStep.rotate 11, CpStep.rotate 12, CpStep.rotate 18, CpStep.rotate 19, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y
  ]

def cf170 : Config :=
  parse false []
[
    CpStep.rotate 38, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf171 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf172 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf173 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y
  ]

def cf174 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y
  ]

def cf175 : Config :=
  parse false []
[
    CpStep.rotate 20, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf176 : Config :=
  parse false []
[
    CpStep.rotate 20, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf177 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf178 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y
  ]

def cf179 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf180 : Config :=
  parse false []
[
    CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf181 : Config :=
  parse false []
[
    CpStep.rotate 7, CpStep.rotate 29, CpStep.rotate 32, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf182 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf183 : Config :=
  parse false []
[
    CpStep.rotate 16, CpStep.rotate 32, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf184 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y
  ]

def cf185 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 31, CpStep.rotate 33, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf186 : Config :=
  parse false []
[
    CpStep.rotate 14, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf187 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.rotate 30, CpStep.rotate 33, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y
  ]

def cf188 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf189 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf190 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf191 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf192 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf193 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.rotate 21, CpStep.rotate 30, CpStep.rotate 33, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf194 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.rotate 10, CpStep.rotate 19, CpStep.rotate 33, CpStep.h,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf195 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf196 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf197 : Config :=
  parse false []
[
    CpStep.rotate 24, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf198 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y
  ]

def cf199 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.rotate 24, CpStep.rotate 30, CpStep.rotate 33, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf200 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf201 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 32, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf202 : Config :=
  parse false []
[
    CpStep.rotate 10, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf203 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.rotate 13, CpStep.rotate 19, CpStep.rotate 20, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf204 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf205 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf206 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf207 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.rotate 19, CpStep.rotate 25, CpStep.rotate 26, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf208 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf209 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf210 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf211 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y
  ]

def cf212 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf213 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf214 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf215 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf216 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 9, CpStep.rotate 15, CpStep.rotate 16, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf217 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 9, CpStep.rotate 15, CpStep.rotate 16, CpStep.h,
    CpStep.rotate 12, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y
  ]

def cf218 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf219 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf220 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf221 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf222 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf223 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf224 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf225 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf226 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.rotate 37, CpStep.h, CpStep.rotate 12, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf227 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf228 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf229 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf230 : Config :=
  parse false []
[
    CpStep.rotate 7, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf231 : Config :=
  parse false []
[
    CpStep.rotate 19, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf232 : Config :=
  parse false []
[
    CpStep.rotate 11, CpStep.rotate 33, CpStep.rotate 37, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf233 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf234 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf235 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf236 : Config :=
  parse false []
[
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf237 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf238 : Config :=
  parse false []
[
    CpStep.rotate 43, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf239 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf240 : Config :=
  parse false []
[
    CpStep.rotate 38, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y
  ]

def cf241 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf242 : Config :=
  parse false []
[
    CpStep.rotate 14, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf243 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf244 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf245 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf246 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 30, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf247 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf248 : Config :=
  parse true []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf249 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf250 : Config :=
  parse false []
[
    CpStep.rotate 20, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf251 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf252 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf253 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y
  ]

def cf254 : Config :=
  parse false []
[
    CpStep.rotate 11, CpStep.rotate 12, CpStep.rotate 33, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf255 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf256 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf257 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf258 : Config :=
  parse false []
[
    CpStep.rotate 24, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf259 : Config :=
  parse false []
[
    CpStep.rotate 4, CpStep.rotate 5, CpStep.rotate 22, CpStep.rotate 29, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf260 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf261 : Config :=
  parse false []
[
    CpStep.rotate 15, CpStep.rotate 16, CpStep.rotate 33, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf262 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf263 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.rotate 26, CpStep.rotate 33, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf264 : Config :=
  parse true []
[
    CpStep.rotate 5, CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf265 : Config :=
  parse false []
[
    CpStep.rotate 14, CpStep.rotate 29, CpStep.rotate 31, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y
  ]

def cf266 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 32, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf267 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf268 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf269 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf270 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf271 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.rotate 19, CpStep.rotate 33, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf272 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y
  ]

def cf273 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf274 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf275 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf276 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf277 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y
  ]

def cf278 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf279 : Config :=
  parse false []
[
    CpStep.rotate 40, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf280 : Config :=
  parse false []
[
    CpStep.rotate 39, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf281 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.rotate 30, CpStep.rotate 33, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf282 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf283 : Config :=
  parse false []
[
    CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf284 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13, CpStep.y,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf285 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf286 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf287 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.rotate 33, CpStep.rotate 37, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf288 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.rotate 12, CpStep.rotate 32, CpStep.rotate 34, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf289 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf290 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf291 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf292 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.rotate 19, CpStep.rotate 37, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf293 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf294 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.rotate 34, CpStep.rotate 36, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf295 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf296 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf297 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 9, CpStep.rotate 30, CpStep.rotate 37, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf298 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.rotate 33, CpStep.rotate 35, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf299 : Config :=
  parse false []
[
    CpStep.rotate 13, CpStep.rotate 31, CpStep.rotate 37, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y
  ]

def cf300 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf301 : Config :=
  parse false []
[
    CpStep.rotate 17, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf302 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.rotate 19, CpStep.rotate 37, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf303 : Config :=
  parse true []
[
    CpStep.rotate 24, CpStep.rotate 29, CpStep.rotate 37, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf304 : Config :=
  parse true []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf305 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y, CpStep.y
  ]

def cf306 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf307 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf308 : Config :=
  parse false []
[
    CpStep.rotate 7, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13, CpStep.h,
    CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y, CpStep.y
  ]

def cf309 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf310 : Config :=
  parse false []
[
    CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y, CpStep.y
  ]

def cf311 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf312 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf313 : Config :=
  parse false []
[
    CpStep.rotate 42, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf314 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf315 : Config :=
  parse false []
[
    CpStep.rotate 42, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf316 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf317 : Config :=
  parse false []
[
    CpStep.rotate 46, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf318 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf319 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf320 : Config :=
  parse false []
[
    CpStep.rotate 14, CpStep.rotate 32, CpStep.rotate 34, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13, CpStep.h,
    CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf321 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 35, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf322 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf323 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf324 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf325 : Config :=
  parse true []
[
    CpStep.rotate 21, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y, CpStep.y
  ]

def cf326 : Config :=
  parse true []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf327 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf328 : Config :=
  parse true []
[
    CpStep.rotate 0, CpStep.rotate 23, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf329 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf330 : Config :=
  parse true []
[
    CpStep.rotate 14, CpStep.rotate 15, CpStep.rotate 21, CpStep.rotate 26, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf331 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf332 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf333 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf334 : Config :=
  parse true []
[
    CpStep.rotate 24, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf335 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf336 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf337 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf338 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf339 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf340 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf341 : Config :=
  parse true []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf342 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.rotate 13, CpStep.rotate 28, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf343 : Config :=
  parse true []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 8, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf344 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf345 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf346 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf347 : Config :=
  parse false []
[
    CpStep.rotate 4, CpStep.rotate 5, CpStep.rotate 24, CpStep.rotate 29, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf348 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf349 : Config :=
  parse true []
[
    CpStep.rotate 24, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y
  ]

def cf350 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf351 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf352 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf353 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y
  ]

def cf354 : Config :=
  parse false []
[
    CpStep.rotate 11, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf355 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf356 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf357 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.rotate 13, CpStep.rotate 29, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf358 : Config :=
  parse false []
[
    CpStep.rotate 16, CpStep.rotate 17, CpStep.rotate 28, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf359 : Config :=
  parse false []
[
    CpStep.rotate 19, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf360 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf361 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf362 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf363 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf364 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf365 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf366 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf367 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf368 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf369 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf370 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf371 : Config :=
  parse true []
[
    CpStep.rotate 4, CpStep.rotate 5, CpStep.rotate 24, CpStep.rotate 29, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y
  ]

def cf372 : Config :=
  parse false []
[
    CpStep.rotate 4, CpStep.rotate 5, CpStep.rotate 18, CpStep.rotate 23, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf373 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf374 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf375 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf376 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf377 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf378 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf379 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf380 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.rotate 33, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf381 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf382 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf383 : Config :=
  parse false []
[
    CpStep.rotate 14, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf384 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf385 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf386 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf387 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf388 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf389 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf390 : Config :=
  parse true []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf391 : Config :=
  parse true []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf392 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf393 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf394 : Config :=
  parse false []
[
    CpStep.rotate 16, CpStep.rotate 17, CpStep.rotate 32, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf395 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf396 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf397 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf398 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf399 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf400 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf401 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf402 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf403 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf404 : Config :=
  parse false []
[
    CpStep.rotate 0, CpStep.rotate 23, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf405 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf406 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf407 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf408 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf409 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf410 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 28, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf411 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf412 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf413 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf414 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf415 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf416 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf417 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf418 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf419 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf420 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf421 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf422 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf423 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf424 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf425 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf426 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf427 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf428 : Config :=
  parse false []
[
    CpStep.rotate 19, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf429 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf430 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf431 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf432 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf433 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf434 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 9, CpStep.rotate 22, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf435 : Config :=
  parse false []
[
    CpStep.rotate 11, CpStep.rotate 12, CpStep.rotate 30, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf436 : Config :=
  parse false []
[
    CpStep.rotate 22, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf437 : Config :=
  parse false []
[
    CpStep.rotate 28, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf438 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf439 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf440 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.rotate 28, CpStep.rotate 32, CpStep.rotate 35, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf441 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf442 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y
  ]

def cf443 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf444 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf445 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf446 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf447 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 9, CpStep.rotate 30, CpStep.rotate 32, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf448 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf449 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf450 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf451 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf452 : Config :=
  parse false []
[
    CpStep.rotate 0, CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf453 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf454 : Config :=
  parse false []
[
    CpStep.rotate 15, CpStep.rotate 30, CpStep.rotate 33, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf455 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf456 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf457 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf458 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf459 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf460 : Config :=
  parse false []
[
    CpStep.rotate 16, CpStep.rotate 17, CpStep.rotate 32, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 5, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf461 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf462 : Config :=
  parse false []
[
    CpStep.rotate 16, CpStep.rotate 17, CpStep.rotate 32, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf463 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.rotate 13, CpStep.rotate 32, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf464 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 32, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf465 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf466 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf467 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf468 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf469 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 13, CpStep.rotate 23, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf470 : Config :=
  parse false []
[
    CpStep.rotate 11, CpStep.rotate 12, CpStep.rotate 33, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf471 : Config :=
  parse false []
[
    CpStep.rotate 19, CpStep.rotate 20, CpStep.rotate 33, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf472 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf473 : Config :=
  parse false []
[
    CpStep.rotate 18, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf474 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf475 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 33, CpStep.rotate 36, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf476 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf477 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.rotate 36, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf478 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.rotate 32, CpStep.rotate 36, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf479 : Config :=
  parse false []
[
    CpStep.rotate 15, CpStep.rotate 16, CpStep.rotate 33, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf480 : Config :=
  parse false []
[
    CpStep.rotate 20, CpStep.rotate 24, CpStep.rotate 36, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf481 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y
  ]

def cf482 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y
  ]

def cf483 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf484 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y
  ]

def cf485 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y
  ]

def cf486 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf487 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13, CpStep.h,
    CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf488 : Config :=
  parse false []
[
    CpStep.rotate 10, CpStep.rotate 11, CpStep.rotate 40, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 13, CpStep.h,
    CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf489 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 31, CpStep.rotate 35, CpStep.rotate 37, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf490 : Config :=
  parse false []
[
    CpStep.rotate 19, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y
  ]

def cf491 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf492 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf493 : Config :=
  parse false []
[
    CpStep.rotate 26, CpStep.rotate 27, CpStep.rotate 37, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 13, CpStep.h,
    CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf494 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf495 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf496 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf497 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf498 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.rotate 34, CpStep.rotate 36, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf499 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf500 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.rotate 37, CpStep.h, CpStep.rotate 12, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y
  ]

def cf501 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf502 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf503 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf504 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf505 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf506 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf507 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y
  ]

def cf508 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf509 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf510 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 9, CpStep.rotate 30, CpStep.rotate 37, CpStep.h,
    CpStep.rotate 12, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf511 : Config :=
  parse false []
[
    CpStep.rotate 21, CpStep.rotate 25, CpStep.rotate 37, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y
  ]

def cf512 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf513 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.rotate 39, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 13, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf514 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf515 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf516 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf517 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf518 : Config :=
  parse false []
[
    CpStep.rotate 25, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf519 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf520 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 31, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf521 : Config :=
  parse false []
[
    CpStep.rotate 2, CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf522 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf523 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf524 : Config :=
  parse false []
[
    CpStep.rotate 3, CpStep.rotate 36, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf525 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf526 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf527 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf528 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf529 : Config :=
  parse true []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf530 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y
  ]

def cf531 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf532 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf533 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.rotate 33, CpStep.rotate 37, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf534 : Config :=
  parse false []
[
    CpStep.rotate 13, CpStep.rotate 20, CpStep.rotate 30, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13, CpStep.h,
    CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf535 : Config :=
  parse false []
[
    CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf536 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf537 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf538 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf539 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf540 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf541 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf542 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf543 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf544 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf545 : Config :=
  parse false []
[
    CpStep.rotate 4, CpStep.rotate 5, CpStep.rotate 36, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf546 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13, CpStep.h,
    CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 10, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf547 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf548 : Config :=
  parse false []
[
    CpStep.rotate 38, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf549 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13, CpStep.y,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 9, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf550 : Config :=
  parse false []
[
    CpStep.rotate 38, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf551 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf552 : Config :=
  parse false []
[
    CpStep.rotate 19, CpStep.rotate 20, CpStep.rotate 40, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf553 : Config :=
  parse false []
[
    CpStep.rotate 36, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 13,
    CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13, CpStep.y,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 10, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf554 : Config :=
  parse false []
[
    CpStep.rotate 40, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf555 : Config :=
  parse false []
[
    CpStep.rotate 37, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf556 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.y
  ]

def cf557 : Config :=
  parse false []
[
    CpStep.rotate 10, CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf558 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.y
  ]

def cf559 : Config :=
  parse false []
[
    CpStep.rotate 32, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf560 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf561 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.y
  ]

def cf562 : Config :=
  parse true []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf563 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf564 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 9, CpStep.rotate 34, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf565 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf566 : Config :=
  parse false []
[
    CpStep.rotate 17, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf567 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf568 : Config :=
  parse true []
[
    CpStep.rotate 24, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y
  ]

def cf569 : Config :=
  parse true []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf570 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf571 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.y
  ]

def cf572 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf573 : Config :=
  parse false []
[
    CpStep.rotate 24, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf574 : Config :=
  parse false []
[
    CpStep.rotate 33, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf575 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.rotate 13, CpStep.rotate 28, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf576 : Config :=
  parse true []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf577 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf578 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf579 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf580 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 5, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf581 : Config :=
  parse true []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf582 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf583 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf584 : Config :=
  parse false []
[
    CpStep.rotate 8, CpStep.rotate 9, CpStep.rotate 33, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf585 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf586 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf587 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 7,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf588 : Config :=
  parse false []
[
    CpStep.rotate 24, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf589 : Config :=
  parse false []
[
    CpStep.rotate 16, CpStep.rotate 17, CpStep.rotate 31, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf590 : Config :=
  parse false []
[
    CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf591 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y
  ]

def cf592 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf593 : Config :=
  parse false []
[
    CpStep.rotate 15, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 7, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 7, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y
  ]

def cf594 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y
  ]

def cf595 : Config :=
  parse false []
[
    CpStep.rotate 41, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 11, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf596 : Config :=
  parse false []
[
    CpStep.rotate 16, CpStep.rotate 17, CpStep.rotate 24, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf597 : Config :=
  parse true []
[
    CpStep.rotate 19, CpStep.rotate 20, CpStep.rotate 36, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 11, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf598 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf599 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf600 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf601 : Config :=
  parse false []
[
    CpStep.rotate 1, CpStep.rotate 2, CpStep.rotate 26, CpStep.rotate 32, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf602 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf603 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf604 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf605 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 9, CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.y,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.y
  ]

def cf606 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf607 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.y
  ]

def cf608 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf609 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.h, CpStep.rotate 4, CpStep.y,
    CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf610 : Config :=
  parse false []
[
    CpStep.rotate 29, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.y
  ]

def cf611 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 8, CpStep.y,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf612 : Config :=
  parse false []
[
    CpStep.rotate 23, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y
  ]

def cf613 : Config :=
  parse false []
[
    CpStep.rotate 16, CpStep.rotate 17, CpStep.rotate 32, CpStep.h, CpStep.rotate 12,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 12, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 4,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf614 : Config :=
  parse false []
[
    CpStep.rotate 11, CpStep.rotate 12, CpStep.rotate 33, CpStep.h, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 13, CpStep.h, CpStep.rotate 13, CpStep.y,
    CpStep.rotate 10, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 11, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf615 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.rotate 13, CpStep.rotate 30, CpStep.rotate 36, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 13, CpStep.y, CpStep.rotate 11,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 6,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf616 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 5, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf617 : Config :=
  parse false []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 4,
    CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf618 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf619 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1,
    CpStep.y
  ]

def cf620 : Config :=
  parse true []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 12, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y, CpStep.rotate 3,
    CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 1, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf621 : Config :=
  parse false []
[
    CpStep.rotate 34, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 12, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 4, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y
  ]

def cf622 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8,
    CpStep.h, CpStep.rotate 8, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y
  ]

def cf623 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 7, CpStep.h, CpStep.rotate 5, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y
  ]

def cf624 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf625 : Config :=
  parse false []
[
    CpStep.rotate 12, CpStep.rotate 13, CpStep.rotate 32, CpStep.h, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 12, CpStep.y, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 6, CpStep.h, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.h,
    CpStep.rotate 10, CpStep.y, CpStep.rotate 8, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 8, CpStep.y, CpStep.rotate 6, CpStep.y,
    CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.rotate 2, CpStep.y
  ]

def cf626 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 5, CpStep.h, CpStep.rotate 7, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf627 : Config :=
  parse true []
[
    CpStep.rotate 30, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 6, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 2,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf628 : Config :=
  parse false []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 12,
    CpStep.y, CpStep.rotate 10, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 4, CpStep.h, CpStep.rotate 10,
    CpStep.h, CpStep.rotate 10, CpStep.h, CpStep.rotate 10, CpStep.y,
    CpStep.rotate 8, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y, CpStep.rotate 4,
    CpStep.h, CpStep.rotate 4, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y
  ]

def cf629 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1, CpStep.h,
    CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y, CpStep.rotate 3,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 5, CpStep.y, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf630 : Config :=
  parse false []
[
    CpStep.rotate 27, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 13,
    CpStep.y, CpStep.rotate 11, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 8, CpStep.h,
    CpStep.rotate 2, CpStep.h, CpStep.rotate 10, CpStep.y, CpStep.rotate 9,
    CpStep.y, CpStep.rotate 7, CpStep.y, CpStep.y, CpStep.rotate 6,
    CpStep.h, CpStep.rotate 6, CpStep.y, CpStep.rotate 2, CpStep.y,
    CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.rotate 2, CpStep.y
  ]

def cf631 : Config :=
  parse false []
[
    CpStep.rotate 31, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 6, CpStep.h, CpStep.rotate 7, CpStep.h, CpStep.rotate 1,
    CpStep.h, CpStep.rotate 1, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 3, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 5,
    CpStep.y, CpStep.rotate 1, CpStep.y, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 1, CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.y, CpStep.rotate 1, CpStep.y
  ]

def cf632 : Config :=
  parse false []
[
    CpStep.rotate 35, CpStep.h, CpStep.rotate 11, CpStep.h, CpStep.rotate 1,
    CpStep.y, CpStep.rotate 3, CpStep.h, CpStep.rotate 11, CpStep.y,
    CpStep.rotate 5, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 10,
    CpStep.y, CpStep.rotate 2, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 4, CpStep.h, CpStep.rotate 8, CpStep.y, CpStep.rotate 2,
    CpStep.h, CpStep.rotate 7, CpStep.y, CpStep.rotate 2, CpStep.h,
    CpStep.rotate 6, CpStep.y, CpStep.rotate 2, CpStep.y, CpStep.y,
    CpStep.rotate 3, CpStep.y, CpStep.y
  ]

def cf633 : Config :=
  parse true []
[
    CpStep.rotate 6, CpStep.h, CpStep.rotate 2, CpStep.h, CpStep.rotate 11,
    CpStep.y, CpStep.rotate 9, CpStep.h, CpStep.rotate 1, CpStep.y,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9,
    CpStep.h, CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.h,
    CpStep.rotate 9, CpStep.h, CpStep.rotate 9, CpStep.y, CpStep.rotate 7,
    CpStep.y, CpStep.y, CpStep.y, CpStep.y, CpStep.y,
    CpStep.y, CpStep.y
  ]

/-- The full list of the 633 reducible configurations.  Coq configuration
number `n` is stored at zero-based index `n - 1`. -/
def theConfigs : List Config :=
[
    cf001, cf002, cf003, cf004, cf005, cf006, cf007, cf008,
    cf009, cf010, cf011, cf012, cf013, cf014, cf015, cf016,
    cf017, cf018, cf019, cf020, cf021, cf022, cf023, cf024,
    cf025, cf026, cf027, cf028, cf029, cf030, cf031, cf032,
    cf033, cf034, cf035, cf036, cf037, cf038, cf039, cf040,
    cf041, cf042, cf043, cf044, cf045, cf046, cf047, cf048,
    cf049, cf050, cf051, cf052, cf053, cf054, cf055, cf056,
    cf057, cf058, cf059, cf060, cf061, cf062, cf063, cf064,
    cf065, cf066, cf067, cf068, cf069, cf070, cf071, cf072,
    cf073, cf074, cf075, cf076, cf077, cf078, cf079, cf080,
    cf081, cf082, cf083, cf084, cf085, cf086, cf087, cf088,
    cf089, cf090, cf091, cf092, cf093, cf094, cf095, cf096,
    cf097, cf098, cf099, cf100, cf101, cf102, cf103, cf104,
    cf105, cf106, cf107, cf108, cf109, cf110, cf111, cf112,
    cf113, cf114, cf115, cf116, cf117, cf118, cf119, cf120,
    cf121, cf122, cf123, cf124, cf125, cf126, cf127, cf128,
    cf129, cf130, cf131, cf132, cf133, cf134, cf135, cf136,
    cf137, cf138, cf139, cf140, cf141, cf142, cf143, cf144,
    cf145, cf146, cf147, cf148, cf149, cf150, cf151, cf152,
    cf153, cf154, cf155, cf156, cf157, cf158, cf159, cf160,
    cf161, cf162, cf163, cf164, cf165, cf166, cf167, cf168,
    cf169, cf170, cf171, cf172, cf173, cf174, cf175, cf176,
    cf177, cf178, cf179, cf180, cf181, cf182, cf183, cf184,
    cf185, cf186, cf187, cf188, cf189, cf190, cf191, cf192,
    cf193, cf194, cf195, cf196, cf197, cf198, cf199, cf200,
    cf201, cf202, cf203, cf204, cf205, cf206, cf207, cf208,
    cf209, cf210, cf211, cf212, cf213, cf214, cf215, cf216,
    cf217, cf218, cf219, cf220, cf221, cf222, cf223, cf224,
    cf225, cf226, cf227, cf228, cf229, cf230, cf231, cf232,
    cf233, cf234, cf235, cf236, cf237, cf238, cf239, cf240,
    cf241, cf242, cf243, cf244, cf245, cf246, cf247, cf248,
    cf249, cf250, cf251, cf252, cf253, cf254, cf255, cf256,
    cf257, cf258, cf259, cf260, cf261, cf262, cf263, cf264,
    cf265, cf266, cf267, cf268, cf269, cf270, cf271, cf272,
    cf273, cf274, cf275, cf276, cf277, cf278, cf279, cf280,
    cf281, cf282, cf283, cf284, cf285, cf286, cf287, cf288,
    cf289, cf290, cf291, cf292, cf293, cf294, cf295, cf296,
    cf297, cf298, cf299, cf300, cf301, cf302, cf303, cf304,
    cf305, cf306, cf307, cf308, cf309, cf310, cf311, cf312,
    cf313, cf314, cf315, cf316, cf317, cf318, cf319, cf320,
    cf321, cf322, cf323, cf324, cf325, cf326, cf327, cf328,
    cf329, cf330, cf331, cf332, cf333, cf334, cf335, cf336,
    cf337, cf338, cf339, cf340, cf341, cf342, cf343, cf344,
    cf345, cf346, cf347, cf348, cf349, cf350, cf351, cf352,
    cf353, cf354, cf355, cf356, cf357, cf358, cf359, cf360,
    cf361, cf362, cf363, cf364, cf365, cf366, cf367, cf368,
    cf369, cf370, cf371, cf372, cf373, cf374, cf375, cf376,
    cf377, cf378, cf379, cf380, cf381, cf382, cf383, cf384,
    cf385, cf386, cf387, cf388, cf389, cf390, cf391, cf392,
    cf393, cf394, cf395, cf396, cf397, cf398, cf399, cf400,
    cf401, cf402, cf403, cf404, cf405, cf406, cf407, cf408,
    cf409, cf410, cf411, cf412, cf413, cf414, cf415, cf416,
    cf417, cf418, cf419, cf420, cf421, cf422, cf423, cf424,
    cf425, cf426, cf427, cf428, cf429, cf430, cf431, cf432,
    cf433, cf434, cf435, cf436, cf437, cf438, cf439, cf440,
    cf441, cf442, cf443, cf444, cf445, cf446, cf447, cf448,
    cf449, cf450, cf451, cf452, cf453, cf454, cf455, cf456,
    cf457, cf458, cf459, cf460, cf461, cf462, cf463, cf464,
    cf465, cf466, cf467, cf468, cf469, cf470, cf471, cf472,
    cf473, cf474, cf475, cf476, cf477, cf478, cf479, cf480,
    cf481, cf482, cf483, cf484, cf485, cf486, cf487, cf488,
    cf489, cf490, cf491, cf492, cf493, cf494, cf495, cf496,
    cf497, cf498, cf499, cf500, cf501, cf502, cf503, cf504,
    cf505, cf506, cf507, cf508, cf509, cf510, cf511, cf512,
    cf513, cf514, cf515, cf516, cf517, cf518, cf519, cf520,
    cf521, cf522, cf523, cf524, cf525, cf526, cf527, cf528,
    cf529, cf530, cf531, cf532, cf533, cf534, cf535, cf536,
    cf537, cf538, cf539, cf540, cf541, cf542, cf543, cf544,
    cf545, cf546, cf547, cf548, cf549, cf550, cf551, cf552,
    cf553, cf554, cf555, cf556, cf557, cf558, cf559, cf560,
    cf561, cf562, cf563, cf564, cf565, cf566, cf567, cf568,
    cf569, cf570, cf571, cf572, cf573, cf574, cf575, cf576,
    cf577, cf578, cf579, cf580, cf581, cf582, cf583, cf584,
    cf585, cf586, cf587, cf588, cf589, cf590, cf591, cf592,
    cf593, cf594, cf595, cf596, cf597, cf598, cf599, cf600,
    cf601, cf602, cf603, cf604, cf605, cf606, cf607, cf608,
    cf609, cf610, cf611, cf612, cf613, cf614, cf615, cf616,
    cf617, cf618, cf619, cf620, cf621, cf622, cf623, cf624,
    cf625, cf626, cf627, cf628, cf629, cf630, cf631, cf632,
    cf633
  ]

theorem length_theConfigs : theConfigs.length = 633 := rfl

private theorem all_theConfigs_static_checks :
    theConfigs.all
      (fun cf =>
        CProg.config cf.program &&
          CfMask.validContractMask cf.contractMask cf.program) = true := by
  fct_decide

theorem all_theConfigs_wellFormed :
    theConfigs.all (fun cf => CProg.config cf.program) = true := by
  apply List.all_eq_true.mpr
  intro cf hcf
  have h := List.all_eq_true.mp all_theConfigs_static_checks cf hcf
  rw [Bool.and_eq_true] at h
  exact h.1

theorem all_theConfigs_validContractMask :
    theConfigs.all
      (fun cf => CfMask.validContractMask cf.contractMask cf.program) =
        true := by
  apply List.all_eq_true.mpr
  intro cf hcf
  have h := List.all_eq_true.mp all_theConfigs_static_checks cf hcf
  rw [Bool.and_eq_true] at h
  exact h.2

theorem wellFormed_of_mem_theConfigs
    {cf : Config}
    (hcf : cf ∈ theConfigs) :
    cf.WellFormed := by
  exact (List.all_eq_true.mp all_theConfigs_wellFormed cf hcf)

theorem cubicProgram_of_mem_theConfigs
    {cf : Config}
    (hcf : cf ∈ theConfigs) :
    cf.CubicProgram :=
  cf.wellFormed_cubicProgram (wellFormed_of_mem_theConfigs hcf)

theorem validContractMask_of_mem_theConfigs
    {cf : Config}
    (hcf : cf ∈ theConfigs) :
    CfMask.validContractMask cf.contractMask cf.program = true :=
  List.all_eq_true.mp all_theConfigs_validContractMask cf hcf

end Config

end FourColor

end Schematic.Math.GraphTheory
