import Counterexample

/-!
# Reproducible proof audit

Run `lake env lean Counterexample/Audit.lean` after `lake build`.
The axiom lists below must contain only Lean's standard foundations:
`propext`, `Classical.choice`, and `Quot.sound`.
-/

#check Counterexample.counterexample
#check Counterexample.exists_precohesive_not_locallyConnected
#check Counterexample.counterexample_specification
#check Precohesion.PresheafReflection.theta_epi_iff_split_units
#check Counterexample.indexing_category_not_finitely_complete

/-- info: 'Counterexample.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Counterexample.counterexample

/-- info: 'Counterexample.exists_precohesive_not_locallyConnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Counterexample.exists_precohesive_not_locallyConnected

/-- info: 'Counterexample.counterexample_specification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Counterexample.counterexample_specification

/-- info: 'Counterexample.canonical_continuity_not_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Counterexample.canonical_continuity_not_mono

/-- info: 'Precohesion.PresheafReflection.theta_epi_iff_split_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Precohesion.PresheafReflection.theta_epi_iff_split_units

/-- info: 'Counterexample.indexing_category_not_finitely_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Counterexample.indexing_category_not_finitely_complete
