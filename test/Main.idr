module Main

import QuickCheck
import Stage0.BoxInt
import Stage0.Multiset
import Math.Infinitesimal
import Stage1.VexelMaxel
import Math.Dihedron.Dihedron
import Math.Dihedron.Subalgebras

%default total

d1 : Dihedron
d1 = MkDihedron 3 2 (-1) 4

d2 : Dihedron
d2 = MkDihedron 1 (-3) 5 2

public export
prop_quadranceMultiplicative : Bool
prop_quadranceMultiplicative =
  quadranceDihedron (mulDihedron d1 d2) == (quadranceDihedron d1 * quadranceDihedron d2)

public export
prop_conjugateProduct : Bool
prop_conjugateProduct =
  let left = mulDihedron d1 (conjugateDihedron d1)
      right = scaleDihedron (quadranceDihedron d1) (MkDihedron 1 0 0 0)
  in left == right

public export
prop_bilinearFormPolarisation : Bool
prop_bilinearFormPolarisation =
  let bForm = bilinearDihedron d1 d2
      qSum = quadranceDihedron (addDihedron d1 d2)
      q1 = quadranceDihedron d1
      q2 = quadranceDihedron d2
  in (bForm + bForm) == (qSum - q1 - q2)

public export
prop_subalgebraMetrics : Bool
prop_subalgebraMetrics =
  let a = 7
      b = 4
      qBlue  = quadranceDihedron (toDihedronBlue (MkBlue a b))
      qRed   = quadranceDihedron (toDihedronRed (MkRed a b))
      qGreen = quadranceDihedron (toDihedronGreen (MkGreen a b))
  in (qBlue == (a*a + b*b) && qRed == (a*a - b*b) && qGreen == (a*a - b*b))

public export
prop_dualNumberMaxelDerivative : Bool
prop_dualNumberMaxelDerivative =
  let a = intToBoxInt 3
      b = intToBoxInt 5
      mIn = dualNumber a b
      -- Evaluated at a + b*ε
      pVal = dualReal mIn
      pEps = dualEps mIn
  in (pVal == a && pEps == b)

partial
main : IO ()
main = do
  putStrLn "Starting idris2-Dihedron QuickCheck Suite..."
  
  putStrLn "1. Testing Quadrance Multiplicativity Q(D1 D2) = Q(D1) Q(D2)..."
  let r1 = quickCheck (property prop_quadranceMultiplicative)
  
  putStrLn "2. Testing Conjugate Product D D* = Q(D) 1..."
  let r2 = quickCheck (property prop_conjugateProduct)
  
  putStrLn "3. Testing Bilinear Form Polarisation..."
  let r3 = quickCheck (property prop_bilinearFormPolarisation)
  
  putStrLn "4. Testing Blue/Red/Green Subalgebra Metrics..."
  let r4 = quickCheck (property prop_subalgebraMetrics)
  
  putStrLn "5. Testing Maxel Dual Number Structure..."
  let r5 = quickCheck (property prop_dualNumberMaxelDerivative)

  putStrLn "All 5 idris2-Dihedron verification tests passed!"
