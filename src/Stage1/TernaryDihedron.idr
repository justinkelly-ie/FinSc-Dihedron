module Stage1.TernaryDihedron

import Language.Reflection
import Stage0.BoxInt
import Stage0.NarayAlphabet
import Stage0.OnSeq.FusedStream
import Stage1.Basis.CoordCell
import Stage1.Dihedron
import Stage1.Basis
import Stage1.DihedronModel

%default total

------------------------------------------------------------------------
-- 1. MONOMORPHIC DEFINITIONALLY REDUCIBLE BALANCED TERNARY ARITHMETIC
------------------------------------------------------------------------

||| 3-Valued Kleene Negation: not(-1) = +1, not(0) = 0, not(+1) = -1.
public export
notBit3 : Bit3 -> Bit3
notBit3 Bit3MinusOne = Bit3PlusOne
notBit3 Bit3Zero     = Bit3Zero
notBit3 Bit3PlusOne  = Bit3MinusOne

||| Monomorphic definitionally reducible addition in F_3.
public export
addBit3 : Bit3 -> Bit3 -> Bit3
addBit3 Bit3Zero     y            = y
addBit3 x            Bit3Zero     = x
addBit3 Bit3PlusOne  Bit3PlusOne  = Bit3MinusOne -- 1 + 1 = 2 = -1 mod 3
addBit3 Bit3MinusOne Bit3MinusOne = Bit3PlusOne  -- -1 + -1 = -2 = 1 mod 3
addBit3 Bit3PlusOne  Bit3MinusOne = Bit3Zero
addBit3 Bit3MinusOne Bit3PlusOne  = Bit3Zero

||| Monomorphic definitionally reducible subtraction in F_3.
public export
subBit3 : Bit3 -> Bit3 -> Bit3
subBit3 x y = addBit3 x (notBit3 y)

||| Monomorphic definitionally reducible multiplication in F_3.
public export
mulBit3 : Bit3 -> Bit3 -> Bit3
mulBit3 Bit3Zero     _            = Bit3Zero
mulBit3 _            Bit3Zero     = Bit3Zero
mulBit3 Bit3PlusOne  y            = y
mulBit3 x            Bit3PlusOne  = x
mulBit3 Bit3MinusOne Bit3MinusOne = Bit3PlusOne

||| Monomorphic equality check on Bit3 reducing definitionally.
public export
eqBit3 : Bit3 -> Bit3 -> Bool
eqBit3 Bit3MinusOne Bit3MinusOne = True
eqBit3 Bit3Zero     Bit3Zero     = True
eqBit3 Bit3PlusOne  Bit3PlusOne  = True
eqBit3 _            _            = False

------------------------------------------------------------------------
-- 2. 2x2 BALANCED TERNARY MATRIX CARRIER (M_2(F_3))
------------------------------------------------------------------------

||| A 2x2 Matrix over balanced ternary field F_3: {-1, 0, +1}.
public export
record TernaryMat2x2 where
  constructor MkTMat
  t00 : Bit3
  t01 : Bit3
  t10 : Bit3
  t11 : Bit3

public export
eqTMat2x2 : TernaryMat2x2 -> TernaryMat2x2 -> Bool
eqTMat2x2 (MkTMat a00 a01 a10 a11) (MkTMat b00 b01 b10 b11) =
  eqBit3 a00 b00 && eqBit3 a01 b01 && eqBit3 a10 b10 && eqBit3 a11 b11

public export
Eq TernaryMat2x2 where
  (==) = eqTMat2x2

public export
Show TernaryMat2x2 where
  show (MkTMat a00 a01 a10 a11) =
    "[[" ++ show a00 ++ ", " ++ show a01 ++ "], [" ++ show a10 ++ ", " ++ show a11 ++ "]]"

||| Addition of two 2x2 ternary matrices in F_3.
public export
addTMat2x2 : TernaryMat2x2 -> TernaryMat2x2 -> TernaryMat2x2
addTMat2x2 (MkTMat a00 a01 a10 a11) (MkTMat b00 b01 b10 b11) =
  MkTMat (addBit3 a00 b00)
         (addBit3 a01 b01)
         (addBit3 a10 b10)
         (addBit3 a11 b11)

||| Negation of a 2x2 ternary matrix in F_3.
public export
negTMat2x2 : TernaryMat2x2 -> TernaryMat2x2
negTMat2x2 (MkTMat a00 a01 a10 a11) =
  MkTMat (notBit3 a00) (notBit3 a01) (notBit3 a10) (notBit3 a11)

||| Multiplication of two 2x2 ternary matrices in F_3:
public export
mulTMat2x2 : TernaryMat2x2 -> TernaryMat2x2 -> TernaryMat2x2
mulTMat2x2 (MkTMat a00 a01 a10 a11) (MkTMat b00 b01 b10 b11) =
  MkTMat
    (addBit3 (mulBit3 a00 b00) (mulBit3 a01 b10))
    (addBit3 (mulBit3 a00 b01) (mulBit3 a01 b11))
    (addBit3 (mulBit3 a10 b00) (mulBit3 a11 b10))
    (addBit3 (mulBit3 a10 b01) (mulBit3 a11 b11))

||| Determinant of a 2x2 ternary matrix in F_3:
||| det(M) = a00 * a11 - a01 * a10.
public export
detTMat2x2 : TernaryMat2x2 -> Bit3
detTMat2x2 (MkTMat a00 a01 a10 a11) =
  subBit3 (mulBit3 a00 a11) (mulBit3 a01 a10)

||| Trace of a 2x2 ternary matrix in F_3:
||| tr(M) = a00 + a11.
public export
trTMat2x2 : TernaryMat2x2 -> Bit3
trTMat2x2 (MkTMat a00 _ _ a11) = addBit3 a00 a11

------------------------------------------------------------------------
-- 3. CANONICAL TERNARY GENERATORS {I, J, K, D}
------------------------------------------------------------------------

||| Identity generator I = [[+1, 0], [0, +1]]:
||| x = +1, t = 0, r = 0, s = 0.
public export
genI : TernaryMat2x2
genI = MkTMat Bit3PlusOne Bit3Zero Bit3Zero Bit3PlusOne

||| Rotation generator J = [[0, -1], [+1, 0]]:
||| x = 0, t = +1, r = 0, s = 0.
||| Satisfies J^2 = -I, det(J) = +1.
public export
genJ : TernaryMat2x2
genJ = MkTMat Bit3Zero Bit3MinusOne Bit3PlusOne Bit3Zero

||| Boost generator K = [[0, +1], [+1, 0]]:
||| x = 0, t = 0, r = +1, s = 0.
||| Satisfies K^2 = +I, det(K) = -1.
public export
genK : TernaryMat2x2
genK = MkTMat Bit3Zero Bit3PlusOne Bit3PlusOne Bit3Zero

||| Boost generator D = [[+1, 0], [0, -1]]:
||| x = 0, t = 0, r = 0, s = +1.
||| Satisfies D^2 = +I, det(D) = -1.
public export
genD : TernaryMat2x2
genD = MkTMat Bit3PlusOne Bit3Zero Bit3Zero Bit3MinusOne

------------------------------------------------------------------------
-- 4. PROPORTION DECOMPOSITION & F_3 GROUPOID RECONSTRUCTION
------------------------------------------------------------------------

||| Constructs a TernaryMat2x2 from proportion components (x; t, r, s) in F_3:
||| mu(x, t, r, s) = [[x + s, r - t], [r + t, x - s]].
public export
fromBit3Proportion : (x : Bit3) -> (t : Bit3) -> (r : Bit3) -> (s : Bit3) -> TernaryMat2x2
fromBit3Proportion x t r s =
  MkTMat (addBit3 x s)
         (subBit3 r t)
         (addBit3 r t)
         (subBit3 x s)

||| Inverts a TernaryMat2x2 to its proportion components (x; t, r, s) in F_3:
||| In F_3, division by 2 is equivalent to negation (since 2 = -1 mod 3).
public export
toBit3Proportion : TernaryMat2x2 -> (Bit3, Bit3, Bit3, Bit3)
toBit3Proportion (MkTMat a00 a01 a10 a11) =
  let x = notBit3 (addBit3 a00 a11)
      s = notBit3 (subBit3 a00 a11)
      r = notBit3 (addBit3 a10 a01)
      t = notBit3 (subBit3 a10 a01)
  in (x, t, r, s)

------------------------------------------------------------------------
-- 5. CONCRETE MORPHISMS (NO TYPE ALIASING)
------------------------------------------------------------------------

||| Converts a Bit3 value to an exact BoxInt.
public export
bit3ToBoxInt : Bit3 -> BoxInt
bit3ToBoxInt Bit3MinusOne = intToBoxInt (-1)
bit3ToBoxInt Bit3Zero     = intToBoxInt 0
bit3ToBoxInt Bit3PlusOne  = intToBoxInt 1

||| Converts an exact BoxInt in {-1, 0, 1} to a Bit3, returning Nothing if out of range.
public export
boxIntToBit3 : BoxInt -> Maybe Bit3
boxIntToBit3 b =
  if b == intToBoxInt (-1) then Just Bit3MinusOne
  else if b == intToBoxInt 0 then Just Bit3Zero
  else if b == intToBoxInt 1 then Just Bit3PlusOne
  else Nothing

||| Converts a TernaryMat2x2 directly into a Substrate Dihedron2 stencil (no type aliasing).
public export
ternaryMatToDihedron2 : TernaryMat2x2 -> Dihedron2
ternaryMatToDihedron2 (MkTMat a00 a01 a10 a11) =
  MkDihedron2 (bit3ToBoxInt a00) (bit3ToBoxInt a01) (bit3ToBoxInt a10) (bit3ToBoxInt a11)

||| Converts a Substrate Dihedron2 stencil into a TernaryMat2x2 if all entries are in {-1, 0, 1}.
public export
dihedron2ToTernaryMat : Dihedron2 -> Maybe TernaryMat2x2
dihedron2ToTernaryMat (MkDihedron2 a00 a01 a10 a11) =
  case (boxIntToBit3 a00, boxIntToBit3 a01, boxIntToBit3 a10, boxIntToBit3 a11) of
    (Just b00, Just b01, Just b10, Just b11) => Just (MkTMat b00 b01 b10 b11)
    _ => Nothing

------------------------------------------------------------------------
-- 6. COMPILE-TIME GROUPOID CLOSURE AUDITS (RULE 01)
------------------------------------------------------------------------

||| Audit: Verifies groupoid closure of {I, J, K, D}:
||| 1. J^2 = -I
||| 2. K^2 = +I
||| 3. D^2 = +I
||| 4. J*K = -D, K*J = +D ({J, K} = 0)
||| 5. K*D = +J, D*K = -J ({K, D} = 0)
||| 6. D*J = -K, J*D = +K ({D, J} = 0)
||| 7. det(I)=+1, det(J)=+1, det(K)=-1, det(D)=-1
public export
auditTernaryGroupoidClosureProof : Bool
auditTernaryGroupoidClosureProof =
  let j2 = mulTMat2x2 genJ genJ
      k2 = mulTMat2x2 genK genK
      d2 = mulTMat2x2 genD genD
      jk = mulTMat2x2 genJ genK
      kj = mulTMat2x2 genK genJ
      kd = mulTMat2x2 genK genD
      dk = mulTMat2x2 genD genK
      dj = mulTMat2x2 genD genJ
      jd = mulTMat2x2 genJ genD
      detI = detTMat2x2 genI
      detJ = detTMat2x2 genJ
      detK = detTMat2x2 genK
      detD = detTMat2x2 genD
  in eqTMat2x2 j2 (negTMat2x2 genI) &&
     eqTMat2x2 k2 genI &&
     eqTMat2x2 d2 genI &&
     eqTMat2x2 jk (negTMat2x2 genD) &&
     eqTMat2x2 kj genD &&
     eqTMat2x2 kd genJ &&
     eqTMat2x2 dk (negTMat2x2 genJ) &&
     eqTMat2x2 dj (negTMat2x2 genK) &&
     eqTMat2x2 jd genK &&
     eqBit3 detI Bit3PlusOne &&
     eqBit3 detJ Bit3PlusOne &&
     eqBit3 detK Bit3MinusOne &&
     eqBit3 detD Bit3MinusOne

||| Audit: Verifies proportion round-trip in F_3:
||| toBit3Proportion (fromBit3Proportion x t r s) == (x, t, r, s)
public export
auditTernaryProportionRoundTripProof : Bool
auditTernaryProportionRoundTripProof =
  let p1 = (Bit3PlusOne, Bit3MinusOne, Bit3Zero, Bit3PlusOne)
      (x, t, r, s) = p1
      mat = fromBit3Proportion x t r s
      (x', t', r', s') = toBit3Proportion mat
  in eqBit3 x x' && eqBit3 t t' && eqBit3 r r' && eqBit3 s s'

||| Audit: Verifies concrete Dihedron2 <-> TernaryMat2x2 embedding round-trip.
public export
auditDihedron2TernaryRoundTripProof : Bool
auditDihedron2TernaryRoundTripProof =
  let d = MkDihedron2 (intToBoxInt 1) (intToBoxInt (-1)) (intToBoxInt 0) (intToBoxInt 1)
  in case dihedron2ToTernaryMat d of
       Just tmat => ternaryMatToDihedron2 tmat == d
       Nothing => False

||| Elaborator reflection helper:
public export
auditTernaryWitness : (prop : Bool) -> Elab (prop = True)
auditTernaryWitness True = pure Refl
auditTernaryWitness False = fail "Compile-time ternary dihedron groupoid audit failed!"

||| Compile-time %macro reflection audit verifying groupoid closure of {I, J, K, D}.
public export
%macro
auditTernaryGroupoidMacro : Elab (Stage1.TernaryDihedron.auditTernaryGroupoidClosureProof = True)
auditTernaryGroupoidMacro = auditTernaryWitness Stage1.TernaryDihedron.auditTernaryGroupoidClosureProof

------------------------------------------------------------------------
-- 7. MATRIX TOKEN STREAMING ISOMORPHISMS (RULE 04 §12)
------------------------------------------------------------------------

||| Streams the 4 matrix pixels of a TernaryMat2x2 in O(1) auxiliary frame.
public export
ternaryMatToStream : TernaryMat2x2 -> FusedStream (Pixel, Bit3)
ternaryMatToStream (MkTMat a00 a01 a10 a11) =
  MkStream next (the Nat 0)
  where
    next : Nat -> Step Nat (Pixel, Bit3)
    next 0 = Yield (mkPixel 1 1, a00) 1
    next 1 = Yield (mkPixel 1 2, a01) 2
    next 2 = Yield (mkPixel 2 1, a10) 3
    next 3 = Yield (mkPixel 2 2, a11) 4
    next _ = Done

||| Folds a deforested stream of (Pixel, Bit3) pairs back into a TernaryMat2x2.
public export
streamToTernaryMat : FusedStream (Pixel, Bit3) -> TernaryMat2x2
streamToTernaryMat strm =
  foldStreamNat 4 updatePixel (MkTMat Bit3Zero Bit3Zero Bit3Zero Bit3Zero) strm
  where
    updatePixel : TernaryMat2x2 -> (Pixel, Bit3) -> TernaryMat2x2
    updatePixel (MkTMat a00 a01 a10 a11) (px, val) =
      if px == mkPixel 1 1 then MkTMat val a01 a10 a11
      else if px == mkPixel 1 2 then MkTMat a00 val a10 a11
      else if px == mkPixel 2 1 then MkTMat a00 a01 val a11
      else if px == mkPixel 2 2 then MkTMat a00 a01 a10 val
      else MkTMat a00 a01 a10 a11

||| Audit: TernaryMat2x2 <-> FusedStream round-trip preserves exact matrix entries.
public export
auditTernaryMatStreamRoundTripProof : Bool
auditTernaryMatStreamRoundTripProof =
  let m = MkTMat Bit3PlusOne Bit3MinusOne Bit3Zero Bit3PlusOne
      strm = ternaryMatToStream m
      m' = streamToTernaryMat strm
  in eqTMat2x2 m m'

------------------------------------------------------------------------
-- 8. DEFORESTED TERNARY GROUPOID ORBIT STREAMS
------------------------------------------------------------------------

||| Generates the discrete sequence of ternary state rotations/boosts under repeated generator multiplication.
public export
streamTernaryOrbit : (fuel : Nat) -> (gen : TernaryMat2x2) -> (init : TernaryMat2x2) -> FusedStream TernaryMat2x2
streamTernaryOrbit fuel gen init =
  MkStream next (Just (fuel, init))
  where
    next : Maybe (Nat, TernaryMat2x2) -> Step (Maybe (Nat, TernaryMat2x2)) TernaryMat2x2
    next Nothing = Done
    next (Just (Z, curr)) = Yield curr Nothing
    next (Just (S k, curr)) = Yield curr (Just (k, mulTMat2x2 curr gen))

||| Audit: J rotation generator orbit has exact period 4 (J^0=I, J^1=J, J^2=-I, J^3=-J, J^4=I).
public export
auditTernaryOrbitPeriodProof : Bool
auditTernaryOrbitPeriodProof =
  let orbitStrm = streamTernaryOrbit 4 genJ genI
      orbit = foldStreamNat 5 (\acc, m => acc ++ [m]) (the (List TernaryMat2x2) []) orbitStrm
  in case orbit of
       [m0, m1, m2, m3, m4] =>
         eqTMat2x2 m0 genI &&
         eqTMat2x2 m1 genJ &&
         eqTMat2x2 m2 (negTMat2x2 genI) &&
         eqTMat2x2 m3 (negTMat2x2 genJ) &&
         eqTMat2x2 m4 genI
       _ => False
