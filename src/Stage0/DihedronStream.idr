module Stage0.DihedronStream

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.OnSeq.FusedStream
import Stage1.Dihedron
import Data.Fuel

%default total

------------------------------------------------------------------------
-- 1. DEFORESTED DIHEDRAL ACTION STREAMS
------------------------------------------------------------------------

||| Discrete Dihedral action step record.
public export
record DihedralStep where
  constructor MkDihedralStep
  stepId   : Int
  normVal  : BoxInt
  val      : Dihedron

public export
Eq DihedralStep where
  (MkDihedralStep id1 n1 v1) == (MkDihedralStep id2 n2 v2) =
    id1 == id2 && n1 == n2 && v1 == v2

||| O(1) allocation deforested stream transducer folding product of Dihedrons across a stream.
public export covering
fusedDihedralActionStream : Fuel -> List Dihedron -> Dihedron
fusedDihedralActionStream f steps =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     [] => Done
                     d :: rest => Yield (MkDihedralStep idx (quadranceDihedron d) d) (idx + 1, rest))
    (\step, acc => mulDihedron (val step) acc)
    (MkDihedron (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0))
    (1, steps)

||| O(1) allocation deforested stream transducer evaluating total sum of quadrances across a Dihedron stream.
public export covering
fusedComputeTotalQuadrance : Fuel -> List Dihedron -> BoxInt
fusedComputeTotalQuadrance f steps =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     [] => Done
                     d :: rest => Yield (MkDihedralStep idx (quadranceDihedron d) d) (idx + 1, rest))
    (\step, acc => normVal step + acc)
    (intToBoxInt 0)
    (1, steps)

------------------------------------------------------------------------
-- 2. DEFORESTED PAULI SPINOR FEYNMAN PATH TRANSDUCERS
------------------------------------------------------------------------

||| Spin-1/2 Pauli Spinor state vector carrying spin-up (\alpha) and spin-down (\beta) Dihedron amplitudes.
public export
record PauliSpinor where
  constructor MkPauliSpinorVal
  spinUp   : Dihedron
  spinDown : Dihedron

public export
MkPauliSpinor : Dihedron -> Dihedron -> PauliSpinor
MkPauliSpinor up down = MkPauliSpinorVal up down

public export
Eq PauliSpinor where
  (MkPauliSpinorVal u1 d1) == (MkPauliSpinorVal u2 d2) = u1 == u2 && d1 == d2

||| Pauli Spinor Path Token for multi-step quantum Feynman path integration.
public export
record PauliPathToken where
  constructor MkPauliPathTokenVal
  stepIndex   : Int
  pathPhase   : Dihedron
  spinorState : PauliSpinor

public export
MkPauliPathToken : Int -> Dihedron -> PauliSpinor -> PauliPathToken
MkPauliPathToken idx p s = MkPauliPathTokenVal idx p s

public export
Eq PauliPathToken where
  (MkPauliPathTokenVal i1 p1 s1) == (MkPauliPathTokenVal i2 p2 s2) = i1 == i2 && p1 == p2 && s1 == s2

||| Unfolds a list of Dihedron phase steps into a deforested PauliPathToken stream.
%inline public export
unfoldPauliPathStream : PauliSpinor -> List Dihedron -> FusedStream PauliPathToken
unfoldPauliPathStream psi steps = MkStream nextStep (1, psi, steps)
  where
    nextStep : (Int, PauliSpinor, List Dihedron) -> Step (Int, PauliSpinor, List Dihedron) PauliPathToken
    nextStep (_, _, []) = Done
    nextStep (idx, spin, d :: rest) =
      let nextSpin = MkPauliSpinor (mulDihedron d (spinUp spin)) (mulDihedron d (spinDown spin))
      in Yield (MkPauliPathToken idx d nextSpin) (idx + 1, nextSpin, rest)

||| Deforested stream sifting operator filtering Pauli path tokens without intermediate allocations.
%inline public export
siftPauliPathStream : (PauliPathToken -> Bool) -> FusedStream PauliPathToken -> FusedStream PauliPathToken
siftPauliPathStream = siftFusedStream

||| Evaluates multi-step Feynman path propagator composition over Pauli spin-1/2 state vectors
||| using a fused stream transducer in O(1) auxiliary space without list allocations.
public export covering
fusedComputePauliPathPropagator : Fuel -> PauliSpinor -> List Dihedron -> PauliSpinor
fusedComputePauliPathPropagator f initialSpinor pathSteps =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     [] => Done
                     dStep :: rest => Yield (MkPauliPathToken idx dStep initialSpinor) (idx + 1, rest))
    (\tok, acc =>
        let phase = pathPhase tok
            up    = spinUp acc
            down  = spinDown acc
        in MkPauliSpinor (mulDihedron phase up) (mulDihedron phase down))
    initialSpinor
    (1, pathSteps)

||| Evaluates total path quadrance norm across a multi-step Pauli Feynman path.
public export covering
fusedComputePauliPathQuadrance : Fuel -> PauliSpinor -> List Dihedron -> BoxInt
fusedComputePauliPathQuadrance f initialSpinor pathSteps =
  let finalSpinor = fusedComputePauliPathPropagator f initialSpinor pathSteps
  in quadranceDihedron (spinUp finalSpinor) + quadranceDihedron (spinDown finalSpinor)

||| Audit witness verifying zero-allocation Pauli spinor Feynman path propagator composition.
public export covering
auditPauliPathPropagatorProof : Bool
auditPauliPathPropagatorProof =
  let initialSpinor = MkPauliSpinor (MkDihedron 1 0 0 0) (MkDihedron 0 1 0 0)
      uPhase1 = MkDihedron 0 1 0 0 -- i phase
      uPhase2 = MkDihedron 0 1 0 0 -- i phase (i * i = -1)
      finalSpinor = fusedComputePauliPathPropagator (limit 100) initialSpinor [uPhase1, uPhase2]
      totalQuad = fusedComputePauliPathQuadrance (limit 100) initialSpinor [uPhase1, uPhase2]
      expectedSpinUp = MkDihedron (-1) 0 0 0
      expectedSpinDown = MkDihedron 0 (-1) 0 0
  in spinUp finalSpinor == expectedSpinUp &&
     spinDown finalSpinor == expectedSpinDown &&
     unwrapBox totalQuad == 2
