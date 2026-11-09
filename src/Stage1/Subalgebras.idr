module Stage1.Subalgebras

import public Stage1.Dihedron
import PhaseUnfolding
import Stage1.Basis.Coordinate

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

||| Parabolic Nilpotent Sub-algebra C_p(F) = {a·1 + b·ε | ε² = 0, det = 0}
public export
record ParabolicDual where
  constructor MkParabolicDual
  real : BoxInt
  eps  : BoxInt

public export
toParabolicDual : Maxel -> ParabolicDual
toParabolicDual m = MkParabolicDual (dualReal m) (dualEps m)

public export
fromParabolicDual : ParabolicDual -> Maxel
fromParabolicDual (MkParabolicDual r e) = dualNumber r e

||| Canonical Nilpotent Infinitesimal Element in the Dihedron algebra:
||| ε = (j - i) / 2 = [[0, 1], [0, 0]].
||| Scaled by 2 as (j - i) for exact integer arithmetic without fraction denominators.
public export
epsilonDihedron : Dihedron
epsilonDihedron = MkDihedron (intToBoxInt 0) (intToBoxInt (-1)) (intToBoxInt 1) (intToBoxInt 0)

||| Audits that ε² = 0 (Grassmann Nilpotency via Dihedron split-quaternion multiplication).
public export
auditEpsilonNilpotentProof : Bool
auditEpsilonNilpotentProof =
  mulDihedron epsilonDihedron epsilonDihedron == MkDihedron (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0)

||| Audits that Quadrance Q(ε) = 0 (det = 0, Parabolic null boundary).
public export
auditEpsilonQuadranceZeroProof : Bool
auditEpsilonQuadranceZeroProof =
  quadranceDihedron epsilonDihedron == intToBoxInt 0

||| Proof witness that ε² = 0 is verified at compile time.
public export
0 prfEpsilonNilpotent : Stage1.Subalgebras.auditEpsilonNilpotentProof = True
prfEpsilonNilpotent = Refl

||| Proof witness that Q(ε) = 0 is verified at compile time.
public export
0 prfEpsilonQuadranceZero : Stage1.Subalgebras.auditEpsilonQuadranceZeroProof = True
prfEpsilonQuadranceZero = Refl

||| Backward-compatibility bridge from Maxel Dual Number to GreenComplex.
public export
fromMaxelDualNumber : Maxel -> GreenComplex
fromMaxelDualNumber m = MkGreen (dualReal m) (dualEps m)
