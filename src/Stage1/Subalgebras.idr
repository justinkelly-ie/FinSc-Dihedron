module Stage1.Subalgebras

import public Stage1.Dihedron
import Transform
import Stage1.VexelMaxel

%default total

||| Blue Complex Sub-algebra C_b(F) = {a + bi | i² = -1}
public export
record BlueComplex where
  constructor MkBlue
  real : BoxInt
  imag : BoxInt

public export
toDihedronBlue : BlueComplex -> Dihedron
toDihedronBlue (MkBlue r i) = MkDihedron r i 0 0

||| Red Complex Sub-algebra C_r(F) = {a + cj | j² = +1}
public export
record RedComplex where
  constructor MkRed
  real : BoxInt
  hyper : BoxInt

public export
toDihedronRed : RedComplex -> Dihedron
toDihedronRed (MkRed r c) = MkDihedron r 0 c 0

||| Green Complex Sub-algebra C_g(F) = {a + dk | k² = +1}
public export
record GreenComplex where
  constructor MkGreen
  real : BoxInt
  diag : BoxInt

public export
toDihedronGreen : GreenComplex -> Dihedron
toDihedronGreen (MkGreen r d) = MkDihedron r 0 0 d

||| Conversion from Maxel Dual Number (where ε² = 0) to Green Degenerate Sub-algebra.
public export
fromMaxelDualNumber : Stage1.VexelMaxel.Maxel -> GreenComplex
fromMaxelDualNumber m = MkGreen (dualReal m) (dualEps m)
