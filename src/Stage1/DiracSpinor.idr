module Stage1.DiracSpinor

import public Stage1.Dihedron
import public Stage1.Basis
import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage1.QuadStream
import public Stage1.FourGeometries

%default total

------------------------------------------------------------------------
-- 1. 4D DISCRETE DIRAC SPINOR & CLIFFORD Cℓ_{1,3}(ℤ) ALGEBRA
------------------------------------------------------------------------

||| Discrete 4-component Dirac Spinor over BoxInt components (ψ0, ψ1, ψ2, ψ3).
public export
record DiracSpinor where
  constructor MkDiracSpinor
  psi0 : BoxInt
  psi1 : BoxInt
  psi2 : BoxInt
  psi3 : BoxInt

public export
Eq DiracSpinor where
  (MkDiracSpinor a1 b1 c1 d1) == (MkDiracSpinor a2 b2 c2 d2) =
    (a1 == a2) && (b1 == b2) && (c1 == c2) && (d1 == d2)

public export
Show DiracSpinor where
  show (MkDiracSpinor a b c d) =
    "Spinor(" ++ show a ++ ", " ++ show b ++ ", " ++ show c ++ ", " ++ show d ++ ")"

||| Embedding of a 4D Dihedron element into a Dirac Spinor.
public export
dihedronToSpinor : Dihedron -> DiracSpinor
dihedronToSpinor (MkDihedronVal a b c d) = MkDiracSpinor a b c d

||| Projection of a Dirac Spinor into a 4D Dihedron element.
public export
spinorToDihedron : DiracSpinor -> Dihedron
spinorToDihedron (MkDiracSpinor a b c d) = MkDihedron a b c d

------------------------------------------------------------------------
-- 2. DISCRETE GAMMA MATRIX OPERATORS
------------------------------------------------------------------------

||| Discrete Gamma-0 operator (timelike / scalar component):
||| γ^0 = diag(1, 1, -1, -1).
public export
gamma0 : DiracSpinor -> DiracSpinor
gamma0 (MkDiracSpinor a b c d) = MkDiracSpinor a b (-c) (-d)

||| Discrete Gamma-1 operator (spacelike Blue / i component).
public export
gamma1 : DiracSpinor -> DiracSpinor
gamma1 (MkDiracSpinor a b c d) = MkDiracSpinor (-d) (-c) b a

||| Discrete Gamma-2 operator (spacelike Red / j component).
public export
gamma2 : DiracSpinor -> DiracSpinor
gamma2 (MkDiracSpinor a b c d) = MkDiracSpinor (-c) d a (-b)

||| Discrete Gamma-3 operator (spacelike Green / k component).
public export
gamma3 : DiracSpinor -> DiracSpinor
gamma3 (MkDiracSpinor a b c d) = MkDiracSpinor b a (-d) (-c)

||| Square of Gamma-0 preserves spinor up to double negation.
public export
gamma0SquareIdentity : DiracSpinor -> DiracSpinor
gamma0SquareIdentity s = gamma0 (gamma0 s)

------------------------------------------------------------------------
-- 3. FUNCTORIAL PROJECTION TO QUAD-STREAM COSMIC MULTISET
------------------------------------------------------------------------

||| Functorially projects a Dihedron onto a 4-channel QuadStreamMultiset payload:
||| - Scalar a -> Elliptic Sector (Bound-state matter)
||| - Blue b   -> Hyperbolic Sector (Gauge flux)
||| - Red c    -> Parabolic Sector (Remainder drain)
||| - Green d  -> Substrate Sector (Irreversible arrow)
public export
dihedronToQuadStream : Dihedron -> QuadStreamMultiset BoxInt
dihedronToQuadStream (MkDihedronVal a b c d) =
  let eMset = if a == 0 then ZeroM else insertItemBox (intToBoxInt 0) a ZeroM
      hMset = if b == 0 then ZeroM else insertItemBox (intToBoxInt 1) b ZeroM
      pMset = if c == 0 then ZeroM else insertItemBox (intToBoxInt 2) c ZeroM
      sMset = if d == 0 then ZeroM else insertItemBox (intToBoxInt 3) d ZeroM
  in MkQuadStream eMset hMset pMset sMset

||| Calculates the total quadrance norm of a Dirac Spinor matching Dihedron quadrance:
||| Q(ψ) = a² + b² - c² - d².
public export
spinorQuadrance : DiracSpinor -> BoxInt
spinorQuadrance (MkDiracSpinor a b c d) = (a * a) + (b * b) - (c * c) - (d * d)

||| Proof witness that Dihedron quadrance equals Dirac Spinor quadrance.
public export
0 prfDihedronSpinorQuadranceEquiv : (d : Dihedron) -> quadranceDihedron d = spinorQuadrance (dihedronToSpinor d)
prfDihedronSpinorQuadranceEquiv (MkDihedronVal a b c d) = Refl
