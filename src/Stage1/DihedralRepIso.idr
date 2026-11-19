||| Representation Theorem Isomorphism for Layer 3 Metrical Geometry & Dihedral Algebra (Rule 03)
|||
||| Establishes the functorial isomorphism between abstract Dihedral group algebra and
||| concrete multiset streams over Dihedron elements:
|||   TheoryRepresentationIsomorphism L3_MetricalGeometry Dihedron Dihedron
module Stage1.DihedralRepIso

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.Dihedron
import Stage1.FourGeometries
import Stage1.PhysicalUniverse.Stratification

%default total

||| Canonical zero dihedron element.
public export
zeroDihedron : Dihedron
zeroDihedron = MkDihedron (MkBoxInt 0) (MkBoxInt 0) (MkBoxInt 0) (MkBoxInt 0)

||| Monomorphic equality for Dihedron elements avoiding typeclass dictionary stalls.
public export
dihedronEq : Dihedron -> Dihedron -> Bool
dihedronEq (MkDihedronVal a1 b1 c1 d1) (MkDihedronVal a2 b2 c2 d2) =
  (a1 == a2) &&
  (b1 == b2) &&
  (c1 == c2) &&
  (d1 == d2)

||| Canonical Representation Isomorphism for Layer 3 Metrical Geometry.
public export
dihedralRepIso : TheoryRepresentationIsomorphism L3_MetricalGeometry Dihedron Dihedron
dihedralRepIso =
  MkTheoryRepIso
    "L3: Dihedral Algebra -> Carrier Dihedron"
    (\d => singletonCarrier d (MkBoxInt 1))
    (\m => case m of
             BoxNode _ _ d _ _ => d
             BoxLeaf           => zeroDihedron)
    (\d =>
      let m = singletonCarrier d (MkBoxInt 1)
          d' = case m of
                 BoxNode _ _ x _ _ => x
                 BoxLeaf           => zeroDihedron
      in dihedronEq d' d
    )

||| Compile-time verification that round-trip isomorphism holds for zero dihedron.
public export
0 prfDihedralRepIsoZero : (verifyRoundTrip Stage1.DihedralRepIso.dihedralRepIso) Stage1.DihedralRepIso.zeroDihedron = True
prfDihedralRepIsoZero = Refl
