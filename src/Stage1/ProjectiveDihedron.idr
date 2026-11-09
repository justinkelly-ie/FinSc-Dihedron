module Stage1.ProjectiveDihedron

import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage1.Dihedron
import public Stage1.Basis
import public Stage1.FourGeometries
import public Stage1.DihedronModel

%default total

------------------------------------------------------------------------
-- 1. 3D MINKOWSKI VECTOR ALGEBRA (Wildberger Section 2)
------------------------------------------------------------------------

||| 3D Minkowski Vector v = (t, r, s) over BoxInt with signature (+, -, -).
public export
record MinkowskiVector where
  constructor MkMVec
  mTime  : BoxInt -- t (timelike coordinate)
  mRed   : BoxInt -- r (first spacelike coordinate)
  mGreen : BoxInt -- s (second spacelike coordinate)

public export
Eq MinkowskiVector where
  (MkMVec t1 r1 s1) == (MkMVec t2 r2 s2) =
    (t1 == t2) && (r1 == r2) && (s1 == s2)

public export
Show MinkowskiVector where
  show (MkMVec t r s) =
    "MVec(" ++ show t ++ ", " ++ show r ++ ", " ++ show s ++ ")"

||| Relativistic Dot Product: <v1, v2> = t1*t2 - r1*r2 - s1*s2.
public export
dotMVec : MinkowskiVector -> MinkowskiVector -> BoxInt
dotMVec (MkMVec t1 r1 s1) (MkMVec t2 r2 s2) =
  (t1 * t2) - (r1 * r2) - (s1 * s2)

||| Relativistic Quadrance: Q(v) = <v, v> = t² - r² - s².
public export
quadranceMVec : MinkowskiVector -> BoxInt
quadranceMVec v = dotMVec v v

||| Relativistic Cross Product (Wildberger Definition 5):
||| v1 × v2 = (r2*s1 - r1*s2, s1*t2 - t1*s2, t1*r2 - t2*r1).
||| First component is negated relative to Euclidean cross product.
public export
crossMVec : MinkowskiVector -> MinkowskiVector -> MinkowskiVector
crossMVec (MkMVec t1 r1 s1) (MkMVec t2 r2 s2) =
  MkMVec ((r2 * s1) - (r1 * s2))
         ((s1 * t2) - (t1 * s2))
         ((t1 * r2) - (t2 * r1))

||| Vector addition for Minkowski vectors.
public export
addMVec : MinkowskiVector -> MinkowskiVector -> MinkowskiVector
addMVec (MkMVec t1 r1 s1) (MkMVec t2 r2 s2) =
  MkMVec (t1 + t2) (r1 + r2) (s1 + s2)

||| Vector negation for Minkowski vectors.
public export
negMVec : MinkowskiVector -> MinkowskiVector
negMVec (MkMVec t r s) = MkMVec (-t) (-r) (-s)

||| Vector subtraction for Minkowski vectors.
public export
subMVec : MinkowskiVector -> MinkowskiVector -> MinkowskiVector
subMVec v1 v2 = addMVec v1 (negMVec v2)

||| Scalar multiplication for Minkowski vectors.
public export
scaleMVec : BoxInt -> MinkowskiVector -> MinkowskiVector
scaleMVec k (MkMVec t r s) = MkMVec (k * t) (k * r) (k * s)

------------------------------------------------------------------------
-- 2. DIHEDRON 2x2 MATRIX ALGEBRA (Wildberger Section 11, Theorem 74)
------------------------------------------------------------------------

||| 2x2 Matrix over BoxInt representing split quaternions / dihedrons.
public export
record DihedronMatrix2x2 where
  constructor MkDMat2x2
  mat11 : BoxInt
  mat12 : BoxInt
  mat21 : BoxInt
  mat22 : BoxInt

public export
Eq DihedronMatrix2x2 where
  (MkDMat2x2 a1 b1 c1 d1) == (MkDMat2x2 a2 b2 c2 d2) =
    (a1 == a2) && (b1 == b2) && (c1 == c2) && (d1 == d2)

public export
Show DihedronMatrix2x2 where
  show (MkDMat2x2 a b c d) =
    "[[" ++ show a ++ ", " ++ show b ++ "], [" ++ show c ++ ", " ++ show d ++ "]]"

||| Canonical isomorphism μ: Dihedron -> M2(F) (Wildberger Definition 73).
||| μ(x, t, r, s) = [[x + s, r - t], [r + t, x - s]]
public export
dihedronToMatrix : Dihedron -> DihedronMatrix2x2
dihedronToMatrix (MkDihedronVal x t r s) =
  MkDMat2x2 (x + s) (r - t) (r + t) (x - s)

||| Inverse isomorphism M2(F) -> Dihedron.
public export
matrixToDihedron : DihedronMatrix2x2 -> Dihedron
matrixToDihedron (MkDMat2x2 a b c d) =
  let x = (a + d) `divBoxInt` 2
      s = (a - d) `divBoxInt` 2
      r = (c + b) `divBoxInt` 2
      t = (c - b) `divBoxInt` 2
  in MkDihedronVal x t r s
  where
    divBoxInt : BoxInt -> Integer -> BoxInt
    divBoxInt bx n = intToBoxInt (unwrapBox bx `div` n)

||| Matrix determinant: det M = mat11*mat22 - mat12*mat21.
public export
detDMat2x2 : DihedronMatrix2x2 -> BoxInt
detDMat2x2 (MkDMat2x2 a b c d) = (a * d) - (b * c)

||| Matrix multiplication for DihedronMatrix2x2.
public export
mulDMat2x2 : DihedronMatrix2x2 -> DihedronMatrix2x2 -> DihedronMatrix2x2
mulDMat2x2 (MkDMat2x2 a1 b1 c1 d1) (MkDMat2x2 a2 b2 c2 d2) =
  MkDMat2x2 ((a1 * a2) + (b1 * c2))
             ((a1 * b2) + (b1 * d2))
             ((c1 * a2) + (d1 * c2))
             ((c1 * b2) + (d1 * d2))

||| Dihedron norm N(α) = x² + t² - r² - s² = x² + Q(v).
public export
dihedronNorm : Dihedron -> BoxInt
dihedronNorm = quadranceDihedron

||| Concrete morphism from DihedronMatrix2x2 to Substrate Dihedron2 stencil (no type aliasing).
public export
dihedronMatrixToDihedron2 : DihedronMatrix2x2 -> Dihedron2
dihedronMatrixToDihedron2 (MkDMat2x2 a b c d) = MkDihedron2 a b c d

||| Concrete morphism from Substrate Dihedron2 stencil to DihedronMatrix2x2 (no type aliasing).
public export
dihedron2ToDihedronMatrix : Dihedron2 -> DihedronMatrix2x2
dihedron2ToDihedronMatrix (MkDihedron2 a b c d) = MkDMat2x2 a b c d

------------------------------------------------------------------------
-- 3. PROJECTIVE DIHEDRON PROPORTIONS (Wildberger Section 11.1)
------------------------------------------------------------------------

||| Projective Dihedron Proportion (x : v) = (x : t : r : s) in P³(Q).
||| Represents a rotation, Lorentz boost, or null rotation without singularities.
public export
record ProjectiveDihedron where
  constructor MkProjDihedron
  projScalar : BoxInt          -- x
  projVec    : MinkowskiVector -- v = (t, r, s)

public export
Eq ProjectiveDihedron where
  (MkProjDihedron x1 v1) == (MkProjDihedron x2 v2) =
    (x1 == x2) && (v1 == v2)

public export
Show ProjectiveDihedron where
  show (MkProjDihedron x v) =
    "ProjDihedron(" ++ show x ++ " : " ++ show v ++ ")"

public export
dihedronToProj : Dihedron -> ProjectiveDihedron
dihedronToProj (MkDihedronVal x t r s) =
  MkProjDihedron x (MkMVec t r s)

public export
projToDihedron : ProjectiveDihedron -> Dihedron
projToDihedron (MkProjDihedron x (MkMVec t r s)) =
  MkDihedronVal x t r s

||| Projective proportion norm N(x : v) = x² + Q(v).
public export
projNorm : ProjectiveDihedron -> BoxInt
projNorm p = dihedronNorm (projToDihedron p)

||| Identity proportion (1 : 0, 0, 0).
public export
idProjDihedron : ProjectiveDihedron
idProjDihedron = MkProjDihedron (intToBoxInt 1) (MkMVec (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0))

||| Projective dihedron group product (Theorem 77):
||| (x : v) ⊗ (y : u) = (xy - <v, u> : xu + yv - v × u).
public export
mulProjDihedron : ProjectiveDihedron -> ProjectiveDihedron -> ProjectiveDihedron
mulProjDihedron (MkProjDihedron x1 v1) (MkProjDihedron x2 v2) =
  let newScalar = (x1 * x2) - dotMVec v1 v2
      term1 = scaleMVec x1 v2
      term2 = scaleMVec x2 v1
      cross = crossMVec v1 v2
      newVec = subMVec (addMVec term1 term2) cross
  in MkProjDihedron newScalar newVec

||| Projective proportion inverse: (x : v)⁻¹ = (x : -v).
public export
invProjDihedron : ProjectiveDihedron -> ProjectiveDihedron
invProjDihedron (MkProjDihedron x v) = MkProjDihedron x (negMVec v)

------------------------------------------------------------------------
-- 4. SANDWICH ACTION ON SPACETIME VECTORS (Wildberger Theorem 78)
------------------------------------------------------------------------

||| Scaled vector action of a projective proportion (x : v) on vector w:
||| w_scaled = (x² - Q(v)) w + 2x (v × w) + 2 <v, w> v.
||| Notice: w_scaled has quadrance Q(w_scaled) = N(α)² * Q(w).
public export
actDihedronVectorScaled : ProjectiveDihedron -> MinkowskiVector -> MinkowskiVector
actDihedronVectorScaled (MkProjDihedron x v) w =
  let qv = quadranceMVec v
      x2MinusQ = (x * x) - qv
      termW = scaleMVec x2MinusQ w
      crossVW = crossMVec v w
      termCross = scaleMVec ((intToBoxInt 2) * x) crossVW
      dotVW = dotMVec v w
      termDot = scaleMVec ((intToBoxInt 2) * dotVW) v
  in addMVec (addMVec termW termCross) termDot

------------------------------------------------------------------------
-- 5. CAUSAL CLASSIFICATION & HALF-SPREAD (Wildberger Section 12.1)
------------------------------------------------------------------------

||| Relativistic Causal Transformation Category (Rule 03 §1 Grounding):
public export
data CausalLorentzType
  = EllipticSpatialRotation -- Timelike axis: Q(v) > 0, 0 < p < 1
  | HyperbolicLorentzBoost  -- Spacelike axis: Q(v) < 0, p < 0
  | ParabolicNullRotation   -- Null axis: Q(v) = 0, p = 0
  | InvolutionHalfTurn      -- Half-turn at infinity: x = 0, p = 1
  | SingularNullDihedron    -- N(x, v) = 0

public export
Eq CausalLorentzType where
  EllipticSpatialRotation == EllipticSpatialRotation = True
  HyperbolicLorentzBoost  == HyperbolicLorentzBoost  = True
  ParabolicNullRotation   == ParabolicNullRotation   = True
  InvolutionHalfTurn      == InvolutionHalfTurn      = True
  SingularNullDihedron    == SingularNullDihedron    = True
  _                       == _                       = False

public export
Show CausalLorentzType where
  show EllipticSpatialRotation = "Elliptic (Spatial Rotation)"
  show HyperbolicLorentzBoost  = "Hyperbolic (Lorentz Boost)"
  show ParabolicNullRotation   = "Parabolic (Null Rotation)"
  show InvolutionHalfTurn      = "Involution (Half Turn)"
  show SingularNullDihedron    = "Singular Null Dihedron"

||| Classifies a projective dihedron into its constructive causal regime.
public export
classifyLorentzTransformation : ProjectiveDihedron -> CausalLorentzType
classifyLorentzTransformation (MkProjDihedron x v) =
  let n = (x * x) + quadranceMVec v
      qv = quadranceMVec v
  in if n == intToBoxInt 0 then SingularNullDihedron
     else if x == intToBoxInt 0 then InvolutionHalfTurn
     else if qv > intToBoxInt 0 then EllipticSpatialRotation
     else if qv < intToBoxInt 0 then HyperbolicLorentzBoost
     else ParabolicNullRotation

------------------------------------------------------------------------
-- 6. SPINORS AS RULINGS OF THE NULL QUADRIC (Wildberger Section 11.2)
------------------------------------------------------------------------

||| Column Spinor κ ∈ Q²: Column projective ruling of the null quadric.
public export
record ColumnSpinor where
  constructor MkColSpinor
  kappa0 : BoxInt
  kappa1 : BoxInt

public export
Eq ColumnSpinor where
  (MkColSpinor a1 b1) == (MkColSpinor a2 b2) = (a1 == a2) && (b1 == b2)

||| Row Spinor ε ∈ Q²: Row projective ruling of the null quadric.
public export
record RowSpinor where
  constructor MkRowSpinor
  eps0 : BoxInt
  eps1 : BoxInt

public export
Eq RowSpinor where
  (MkRowSpinor a1 b1) == (MkRowSpinor a2 b2) = (a1 == a2) && (b1 == b2)

||| Constructs rank-1 matrix from column spinor κ and row spinor ε:
||| μ(α) = κ ⊗ ε = [[kappa0 * eps0, kappa0 * eps1], [kappa1 * eps0, kappa1 * eps1]].
public export
spinorOuterProduct : ColumnSpinor -> RowSpinor -> DihedronMatrix2x2
spinorOuterProduct (MkColSpinor k0 k1) (MkRowSpinor e0 e1) =
  MkDMat2x2 (k0 * e0) (k0 * e1) (k1 * e0) (k1 * e1)

||| Verifies that any matrix constructed from a spinor outer product has determinant 0 (null quadric).
public export
prop_spinorMatrixDeterminantNull : ColumnSpinor -> RowSpinor -> Bool
prop_spinorMatrixDeterminantNull k e =
  detDMat2x2 (spinorOuterProduct k e) == intToBoxInt 0

------------------------------------------------------------------------
-- 7. CANONICAL RATIONAL BOOST & ROTATION CONSTRUCTORS (Wildberger Sec. 11-12)
------------------------------------------------------------------------

||| Constructs a pure spatial rotation proportion around the time axis (fixing time t, rotating spatial plane (r, s)):
||| Vector v = (t, 0, 0), Q(v) = t^2 > 0 (Elliptic).
||| Matrix: [[x, -t], [t, x]], Det: x^2 + t^2, Half-spread: p = t^2 / (x^2 + t^2).
public export
mkRationalSpatialRotation : (x : BoxInt) -> (t : BoxInt) -> ProjectiveDihedron
mkRationalSpatialRotation x t =
  MkProjDihedron x (MkMVec t (intToBoxInt 0) (intToBoxInt 0))

||| Constructs a pure relativistic Lorentz boost along the s-axis:
||| Vector v = (0, 0, s), Q(v) = -s^2 < 0 (Hyperbolic).
||| Matrix: [[x + s, 0], [0, x - s]], Det: x^2 - s^2, Velocity beta = 2xs / (x^2 + s^2).
public export
mkRationalBoostS : (x : BoxInt) -> (s : BoxInt) -> ProjectiveDihedron
mkRationalBoostS x s =
  MkProjDihedron x (MkMVec (intToBoxInt 0) (intToBoxInt 0) s)

||| Constructs a pure relativistic Lorentz boost along the r-axis:
||| Vector v = (0, r, 0), Q(v) = -r^2 < 0 (Hyperbolic).
||| Matrix: [[x, r], [r, x]], Det: x^2 - r^2, Velocity beta = 2xr / (x^2 + r^2).
public export
mkRationalBoostR : (x : BoxInt) -> (r : BoxInt) -> ProjectiveDihedron
mkRationalBoostR x r =
  MkProjDihedron x (MkMVec (intToBoxInt 0) r (intToBoxInt 0))

||| Constructs an arbitrary relativistic Lorentz boost in spatial direction (r, s):
||| Vector v = (0, r, s), Q(v) = -r^2 - s^2 < 0 (Hyperbolic).
||| Matrix: [[x + s, r], [r, x - s]], Det: x^2 - r^2 - s^2.
public export
mkArbitraryRationalBoost : (x : BoxInt) -> (r : BoxInt) -> (s : BoxInt) -> ProjectiveDihedron
mkArbitraryRationalBoost x r s =
  MkProjDihedron x (MkMVec (intToBoxInt 0) r s)

||| Constructs an exact relativistic boost with rational velocity beta = a/c
||| derived directly from a Pythagorean triad a^2 + b^2 = c^2 without square roots or gamma factor:
||| Sets x = c + b and r = a.
||| Then 2xr / (x^2 + r^2) = 2(c+b)a / ((c+b)^2 + a^2) = 2a(c+b) / (2c(c+b)) = a/c = beta!
public export
mkVelocityBoostFromTriad : (a : BoxInt) -> (b : BoxInt) -> (c : BoxInt) -> ProjectiveDihedron
mkVelocityBoostFromTriad a b c =
  mkRationalBoostR (c + b) a

||| Constructs an exact Parabolic Null Rotation (lightcone shear):
||| Vector v = (s, 0, s), Q(v) = s^2 - 0 - s^2 = 0 (Parabolic).
||| Matrix: [[x + s, -s], [s, x - s]], Det: x^2.
public export
mkParabolicNullRotation : (x : BoxInt) -> (s : BoxInt) -> ProjectiveDihedron
mkParabolicNullRotation x s =
  MkProjDihedron x (MkMVec s (intToBoxInt 0) s)

------------------------------------------------------------------------
-- 8. WIGNER-THOMAS ROTATION THEOREM (Wildberger Theorem 70 & 79)
------------------------------------------------------------------------

||| Proves that the product of two non-collinear pure boosts (boost along r and boost along s)
||| produces a non-zero timelike vector component t = - (r1 * s2) != 0,
||| inducing an exact rational spatial rotation (Wigner-Thomas precession):
public export
wignerThomasCrossComponent : (r : BoxInt) -> (s : BoxInt) -> BoxInt
wignerThomasCrossComponent r s = - (r * s)

||| Evaluates the product of a boost along r and a boost along s:
public export
composeNonCollinearBoosts : (x1, r1 : BoxInt) -> (x2, s2 : BoxInt) -> ProjectiveDihedron
composeNonCollinearBoosts x1 r1 x2 s2 =
  let b1 = mkRationalBoostR x1 r1
      b2 = mkRationalBoostS x2 s2
  in mulProjDihedron b1 b2

||| Audit: Verifies that composing non-collinear boosts produces Thomas precession (t != 0)
||| and that reversing the order reverses the sign of Thomas precession (t12 = -t21):
public export
auditWignerThomasPrecessionProof : Bool
auditWignerThomasPrecessionProof =
  let x1 = intToBoxInt 2; r1 = intToBoxInt 1  -- boost in r
      x2 = intToBoxInt 3; s2 = intToBoxInt 1  -- boost in s
      b1 = mkRationalBoostR x1 r1
      b2 = mkRationalBoostS x2 s2
      prod12 = mulProjDihedron b1 b2
      prod21 = mulProjDihedron b2 b1
      t12 = prod12.projVec.mTime
      t21 = prod21.projVec.mTime
      triadBoost = mkVelocityBoostFromTriad (intToBoxInt 3) (intToBoxInt 4) (intToBoxInt 5)
      triadN = projNorm triadBoost
      nullRot = mkParabolicNullRotation (intToBoxInt 3) (intToBoxInt 2)
      nullQ = quadranceMVec nullRot.projVec
  in (t12 == intToBoxInt 1) && (t21 == intToBoxInt (-1)) && (t12 == - t21) &&
     (triadN == intToBoxInt 72) &&
     (nullQ == intToBoxInt 0)

