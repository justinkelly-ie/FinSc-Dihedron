module FinScDihedron.ProjectiveRotation

import Data.Vect
import FinScBox.BoxInt

%default total

------------------------------------------------------------------------
-- 1. 3D PROJECTIVE ROTATION PROPORTIONS (WILDBERGER SO(3; Q))
------------------------------------------------------------------------

||| A Projective Rotation Proportion `(x : t : r : s)`:
||| Parameterizes an exact 3D rational rotation without continuous angles or square roots,
||| forming the rational `SO(3; Q)` spatial observer frame alongside `SL(2; Q)` Dihedrons.
public export
record ProjectiveProportion where
  constructor MkProjectiveProportion
  xCoord : BoxInt
  tCoord : BoxInt
  rCoord : BoxInt
  sCoord : BoxInt

public export
Eq ProjectiveProportion where
  (MkProjectiveProportion x1 t1 r1 s1) == (MkProjectiveProportion x2 t2 r2 s2) =
    x1 == x2 && t1 == t2 && r1 == r2 && s1 == s2

public export
Show ProjectiveProportion where
  show (MkProjectiveProportion x t r s) =
    "(" ++ show x ++ " : " ++ show t ++ " : " ++ show r ++ " : " ++ show s ++ ")"

||| Identity rotation: `(1 : 0 : 0 : 0)`.
public export
idProportion : ProjectiveProportion
idProportion = MkProjectiveProportion (MkBoxInt 1) (MkBoxInt 0) (MkBoxInt 0) (MkBoxInt 0)

||| Exact 3D vector cross product `v1 x v2`.
public export
crossProduct3 : Vect 3 BoxInt -> Vect 3 BoxInt -> Vect 3 BoxInt
crossProduct3 [t1, r1, s1] [t2, r2, s2] =
  [ (r1 * s2) - (s1 * r2)
  , (s1 * t2) - (t1 * s2)
  , (t1 * r2) - (r1 * t2)
  ]

||| Exact dot product of two 3D vectors: `v1 . v2`.
public export
dotProduct3 : Vect 3 BoxInt -> Vect 3 BoxInt -> BoxInt
dotProduct3 [t1, r1, s1] [t2, r2, s2] =
  (t1 * t2) + (r1 * r2) + (s1 * s2)

||| Exact quaternion composition of two projective proportions: `p2 * p1`.
public export
composeProportion : ProjectiveProportion -> ProjectiveProportion -> ProjectiveProportion
composeProportion (MkProjectiveProportion x2 t2 r2 s2)
                  (MkProjectiveProportion x1 t1 r1 s1) =
  let v1 = [t1, r1, s1]
      v2 = [t2, r2, s2]
      xOut = (x1 * x2) - dotProduct3 v1 v2
      [tCross, rCross, sCross] = crossProduct3 v2 v1
      tOut = (x1 * t2) + (x2 * t1) + tCross
      rOut = (x1 * r2) + (x2 * r1) + rCross
      sOut = (x1 * s2) + (x2 * s1) + sCross
  in MkProjectiveProportion xOut tOut rOut sOut

||| Inverse rotation proportion: `(x : -t : -r : -s)`.
public export
inverseProportion : ProjectiveProportion -> ProjectiveProportion
inverseProportion (MkProjectiveProportion x t r s) =
  MkProjectiveProportion x (negate t) (negate r) (negate s)

------------------------------------------------------------------------
-- 2. ROTATION MATRIX GENERATION & VECTOR ACTION
------------------------------------------------------------------------

||| Produces the exact 3x3 scaled rational rotation matrix:
||| `R_scaled = (x^2 - Q(v)) I + 2 v v^T + 2 x [v]_x`
public export
rotationMatrixScaled3 : ProjectiveProportion -> Vect 3 (Vect 3 BoxInt)
rotationMatrixScaled3 (MkProjectiveProportion x t r s) =
  let x2 = x * x
      t2 = t * t
      r2 = r * r
      s2 = s * s
      two = MkBoxInt 2
      row1 = [ x2 + t2 - r2 - s2
             , (two * (t * r)) - (two * (x * s))
             , (two * (t * s)) + (two * (x * r))
             ]
      row2 = [ (two * (t * r)) + (two * (x * s))
             , x2 - t2 + r2 - s2
             , (two * (r * s)) - (two * (x * t))
             ]
      row3 = [ (two * (t * s)) - (two * (x * r))
             , (two * (r * s)) + (two * (x * t))
             , x2 - t2 - r2 + s2
             ]
  in [row1, row2, row3]

||| Rotates a 3D vector by a projective proportion.
public export
rotateVectorScaled : ProjectiveProportion -> Vect 3 BoxInt -> Vect 3 BoxInt
rotateVectorScaled p [v1, v2, v3] =
  let [r1, r2, r3] = rotationMatrixScaled3 p
  in [ dotProduct3 r1 [v1, v2, v3]
     , dotProduct3 r2 [v1, v2, v3]
     , dotProduct3 r3 [v1, v2, v3]
     ]

------------------------------------------------------------------------
-- 3. HOUSEHOLDER MEAN REFLECTION & EQUILATERAL SPREAD
------------------------------------------------------------------------

||| Symmetric 3D Householder mean-reflection matrix (scaled by 3):
||| `2 J_3 - 3 I_3 = [[-1, 2, 2], [2, -1, 2], [2, 2, -1]]`
public export
meanReflectionScaled3 : Vect 3 (Vect 3 BoxInt)
meanReflectionScaled3 =
  let m1 = MkBoxInt (-1)
      p2 = MkBoxInt 2
  in [ [m1, p2, p2]
     , [p2, m1, p2]
     , [p2, p2, m1]
     ]

||| Applies the scaled 3D mean reflection to a 3-element vector (`M(M(v)) = 9 v`).
public export
applyMeanReflectionScaled3 : Vect 3 BoxInt -> Vect 3 BoxInt
applyMeanReflectionScaled3 [v1, v2, v3] =
  let [r1, r2, r3] = meanReflectionScaled3
  in [ dotProduct3 r1 [v1, v2, v3]
     , dotProduct3 r2 [v1, v2, v3]
     , dotProduct3 r3 [v1, v2, v3]
     ]

||| Compile-time QTT 0 verification of Wildberger's Triple Spread Formula for `(3/4, 3/4, 3/4)`:
||| `(s1 + s2 + s3)^2 = 2(s1^2 + s2^2 + s3^2) + 4 s1 s2 s3`.
public export
0 prfTripleSpreadEquilateral :
  (let sNum = 3
       sDen = 4
       lhs = (3 * sNum) * (3 * sNum) * (sDen * sDen)
       rhs1 = 2 * (3 * (sNum * sNum)) * (sDen * sDen)
       rhs2 = 4 * (sNum * sNum * sNum) * sDen
   in lhs == rhs1 + rhs2) = True
prfTripleSpreadEquilateral = Refl
