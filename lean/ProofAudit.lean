import Cohesion
import ToposPort
import Positive
import Counterexample
import RealContinuity
import PointlessEnd
import ModalForm
import Lean.Util.CollectAxioms

/-! Exhaustive axiom audit of the imported project namespaces. -/

open Lean Elab Command

set_option maxRecDepth 10000
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : List Name := [`Cohesion, `ToposPort, `Positive, `Counterexample, `Precohesion, `RealContinuity, `PointlessEnd, `ModalForm]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      let dependencies ← Lean.collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do
          throwError "Unexpected axiom {dependency} in {name}"
      count := count + 1
  logInfo m!"Audited {count} declarations: all axiom dependencies are among propext, Classical.choice, Quot.sound."
