import Cohesion.Continuity

/-! # Compatibility names for the shared Continuity interface

The canonical definitions and their evaluation identities live in
`Cohesion.Continuity`, shared by the positive theorem and the counterexample.
-/

namespace Positive

export Cohesion (prodComparison_natTrans prodComparison_natTrans_assoc
  inv_prodComparison_natTrans inv_prodComparison_natTrans_assoc
  expComparison_natTrans expComparison_natTrans_assoc)

namespace PrecohesiveMorphism

export Cohesion.PrecohesiveMorphism (theta theta_epi continuityComparison
  EpicContinuity MonicContinuity unit_theta pointsExponentialComparison
  continuity_theta epi_theta_power)

end PrecohesiveMorphism
end Positive
