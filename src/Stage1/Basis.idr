module Stage1.Basis

import public Stage0.Multiset
import public Stage0.BoxInt

%default total

||| Canonical 4D Dihedron Basis elements {1, i, j, k}.
public export
data DihedronBasis = One | I | J | K

public export
Eq DihedronBasis where
  One == One = True
  I == I = True
  J == J = True
  K == K = True
  _ == _ = False

public export
Show DihedronBasis where
  show One = "1"
  show I   = "i"
  show J   = "j"
  show K   = "k"

||| Multiplication table of basis elements returning (sign, product_basis).
public export
mulBasis : DihedronBasis -> DihedronBasis -> (BoxInt, DihedronBasis)
mulBasis One b   = (1, b)
mulBasis b One   = (1, b)
mulBasis I I     = (-1, One)
mulBasis J J     = (1, One)
mulBasis K K     = (1, One)
mulBasis I J     = (-1, K)
mulBasis J I     = (1, K)
mulBasis J K     = (1, I)
mulBasis K J     = (-1, I)
mulBasis K I     = (-1, J)
mulBasis I K     = (1, J)
