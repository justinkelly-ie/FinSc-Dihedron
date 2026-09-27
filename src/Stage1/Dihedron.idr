module Stage1.Dihedron

import public Stage1.Basis
import public Stage0.BoxInt
import public Stage0.Multiset
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel


%default total

||| A Dihedron element D = a·1 + b·i + c·j + d·k over scalar payload.
public export
record DihedronVal scalar where
  constructor MkDihedronVal
  scalarA : scalar -- Scalar (1)
  blueB   : scalar -- Blue (i, i² = -1)
  redC    : scalar -- Red (j, j² = +1)
  greenD  : scalar -- Green (k, k² = +1)

public export
Dihedron : Type
Dihedron = DihedronVal BoxInt

public export
MkDihedron : BoxInt -> BoxInt -> BoxInt -> BoxInt -> Dihedron
MkDihedron a b c d = MkDihedronVal a b c d

public export
a : DihedronVal scalar -> scalar
a (MkDihedronVal s _ _ _) = s

public export
b : DihedronVal scalar -> scalar
b (MkDihedronVal _ bl _ _) = bl

public export
c : DihedronVal scalar -> scalar
c (MkDihedronVal _ _ r _) = r

public export
d : DihedronVal scalar -> scalar
d (MkDihedronVal _ _ _ g) = g

public export
(Eq scalar) => Eq (DihedronVal scalar) where
  (MkDihedronVal a1 b1 c1 d1) == (MkDihedronVal a2 b2 c2 d2) =
    (a1 == a2) && (b1 == b2) && (c1 == c2) && (d1 == d2)

public export
(Show scalar) => Show (DihedronVal scalar) where
  show (MkDihedronVal a b c d) =
    show a ++ " + " ++ show b ++ "i + " ++ show c ++ "j + " ++ show d ++ "k"

------------------------------------------------------------------------
-- FUNCTOR, APPLICATIVE & MONAD IMPLEMENTATIONS
------------------------------------------------------------------------

public export
Functor DihedronVal where
  map f (MkDihedronVal a b c d) = MkDihedronVal (f a) (f b) (f c) (f d)

public export
Applicative DihedronVal where
  pure x = MkDihedronVal x x x x
  (MkDihedronVal f g h k) <*> (MkDihedronVal a b c d) =
    MkDihedronVal (f a) (g b) (h c) (k d)

public export
Monad DihedronVal where
  (MkDihedronVal a b c d) >>= f =
    MkDihedronVal (scalarA (f a)) (blueB (f b)) (redC (f c)) (greenD (f d))

------------------------------------------------------------------------
-- ALGEBRAIC INTERFACES (SEMIGROUP & MONOID)
------------------------------------------------------------------------

||| Addition of Dihedrons.
public export
addDihedron : Dihedron -> Dihedron -> Dihedron
addDihedron (MkDihedronVal a1 b1 c1 d1) (MkDihedronVal a2 b2 c2 d2) =
  MkDihedronVal (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2)

||| Negation of Dihedron.
public export
negDihedron : Dihedron -> Dihedron
negDihedron (MkDihedronVal a b c d) =
  MkDihedronVal (-a) (-b) (-c) (-d)

||| Subtraction of Dihedrons.
public export
subDihedron : Dihedron -> Dihedron -> Dihedron
subDihedron d1 d2 = addDihedron d1 (negDihedron d2)

||| Multiplication of Dihedrons via basis multiplication table.
public export
mulDihedron : Dihedron -> Dihedron -> Dihedron
mulDihedron (MkDihedronVal a1 b1 c1 d1) (MkDihedronVal a2 b2 c2 d2) =
  let resA = (a1 * a2) - (b1 * b2) + (c1 * c2) + (d1 * d2)
      resB = (a1 * b2) + (b1 * a2) + (c1 * d2) - (d1 * c2)
      resC = (a1 * c2) + (c1 * a2) - (b1 * d2) + (d1 * b2)
      resD = (a1 * d2) + (d1 * a2) - (b1 * c2) + (c1 * b2)
  in MkDihedronVal resA resB resC resD

||| Additive Semigroup instance for Dihedron.
public export
Semigroup Dihedron where
  (<+>) = addDihedron

||| Additive Monoid instance for Dihedron.
public export
Monoid Dihedron where
  neutral = MkDihedron 0 0 0 0

||| Multiplicative Semigroup named implementation for Dihedron.
public export
[MultDihedronSemigroup] Semigroup Dihedron where
  (<+>) = mulDihedron

||| Multiplicative Monoid named implementation for Dihedron.
public export
[MultDihedronMonoid] Monoid Dihedron where
  neutral = MkDihedron 1 0 0 0

||| Scalar multiplication.
public export
scaleDihedron : BoxInt -> Dihedron -> Dihedron
scaleDihedron s (MkDihedronVal a b c d) =
  MkDihedronVal (s * a) (s * b) (s * c) (s * d)

||| Half-Trace T(D) = a
public export
halfTrace : Dihedron -> BoxInt
halfTrace (MkDihedronVal a _ _ _) = a

||| Conjugation D* = a - bi - cj - dk
public export
conjugateDihedron : Dihedron -> Dihedron
conjugateDihedron (MkDihedronVal a b c d) =
  MkDihedronVal a (-b) (-c) (-d)

||| Quadrance (Determinant) Q(D) = a² + b² - c² - d²
public export
quadranceDihedron : Dihedron -> BoxInt
quadranceDihedron (MkDihedronVal a b c d) =
  (a * a) + (b * b) - (c * c) - (d * d)

||| Symmetric bilinear form <D1, D2> = T(D1 * D2*)
public export
bilinearDihedron : Dihedron -> Dihedron -> BoxInt
bilinearDihedron d1 d2 = halfTrace (mulDihedron d1 (conjugateDihedron d2))

public export
Num Dihedron where
  (+) = addDihedron
  (*) = mulDihedron
  fromInteger n = MkDihedron (fromInteger n) 0 0 0

public export
Neg Dihedron where
  negate = negDihedron
  (-) = subDihedron

------------------------------------------------------------------------
-- 2. COMPILE-TIME DIHEDRAL SYMMETRY WITNESSES
------------------------------------------------------------------------

||| Evaluates discrete norm quadrance conservation under Dihedral conjugation: Q(D*) == Q(D).
public export
isDihedralConjugateNormPreserved : Dihedron -> Bool
isDihedralConjugateNormPreserved d =
  quadranceDihedron (conjugateDihedron d) == quadranceDihedron d

||| Erased compile-time proof witness verifying Dihedral norm invariance under algebra conjugation.
public export
0 DihedralInvarianceWitness : Dihedron -> Type
DihedralInvarianceWitness d = isDihedralConjugateNormPreserved d = True

||| Static compile-time witness for baseline Dihedron element (1 + 2i + 3j + 4k).
public export
0 prfDihedronConjugateNormInvariance : DihedralInvarianceWitness (MkDihedron (intToBoxInt 1) (intToBoxInt 2) (intToBoxInt 3) (intToBoxInt 4))
prfDihedronConjugateNormInvariance = Refl

||| Bounded Dihedral state carrying compile-time erased symmetry witness.
public export
record BoundedDihedralState (d : Dihedron) where
  constructor MkBoundedDihedralState
  dihedronVal : Dihedron
  0 symmetryPrf : DihedralInvarianceWitness d

------------------------------------------------------------------------
-- 3. 2LTT STAGING CODE GENERATOR TRANSDUCER
------------------------------------------------------------------------

||| Deforested 2LTT staged code generator transducer for hypercomplex Dihedron multiplication.
%inline public export
stagedMulDihedron : Dihedron -> Dihedron -> Code Dihedron
stagedMulDihedron d1 d2 = quote (mulDihedron d1 d2)

||| QTT 0 erased proof witness verifying Dihedron multiplication staging inverse identity.
public export
0 prfStagedMulDihedron : (d1, d2 : Dihedron) -> splice (stagedMulDihedron d1 d2) = mulDihedron d1 d2
prfStagedMulDihedron d1 d2 = inverseSpliceQuote (mulDihedron d1 d2)

