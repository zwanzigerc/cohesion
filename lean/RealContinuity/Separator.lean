import RealContinuity.FiniteHeight

/-!
# The abstract finite-height separator

For a tower of spaces `B n` with points `b n`, `t n` that are distinct at
height `n`, the tuples `b` and `t` of the EXTERNAL topological product
`T = ∏ B n` do not have finite height in `T`. A putative equality at height
`m` projects to an equality at height `m` in `B m`.

`D_* = points(T)/FiniteHeight` is only a quotient SET; no topology on it is
used, and no continuity of the class map on `T` is asserted. For a continuous
`f : U → T` out of a nonempty space of pairwise finite height, the class of
`f u` does not depend on `u` and is natural in `U`.
-/

noncomputable section

namespace RealContinuity

universe u

/-- The quotient set of points of `X` by finite height. -/
def FHQuot (X : TopCat.{u}) : Type u := Quotient (finiteHeightSetoid X)

/-- The class of a point. -/
def fhClass {X : TopCat.{u}} (x : X) : FHQuot X := Quotient.mk (finiteHeightSetoid X) x

theorem fhClass_eq_iff {X : TopCat.{u}} {x y : X} :
    fhClass x = fhClass y ↔ FiniteHeight X x y :=
  Quotient.eq (r := finiteHeightSetoid X)

/-- The external product of a tower. -/
abbrev towerProduct (B : ℕ → TopCat.{u}) : TopCat.{u} := TopCat.of ((n : ℕ) → B n)

/-- The separator: tuples separated at height `n` in the `n`-th factor have
infinite height in the product. -/
theorem not_finiteHeight_pi (B : ℕ → TopCat.{u}) (b t : (n : ℕ) → B n)
    (hsep : ∀ n, etaIter n (B n) (b n) ≠ etaIter n (B n) (t n)) :
    ¬ FiniteHeight (towerProduct B) b t := by
  rintro ⟨m, hm⟩
  let π : C(towerProduct B, B m) := ⟨fun x => x m, continuous_apply m⟩
  exact hsep m (etaIter_map_eq π hm)

theorem fhClass_ne_of_separated (B : ℕ → TopCat.{u}) (b t : (n : ℕ) → B n)
    (hsep : ∀ n, etaIter n (B n) (b n) ≠ etaIter n (B n) (t n)) :
    fhClass (X := towerProduct B) b ≠ fhClass (X := towerProduct B) t :=
  fun h => not_finiteHeight_pi B b t hsep (fhClass_eq_iff.mp h)

/-- Unbounded depth (the hypothesis of the Agda conditional refutation
`gist.RealCohesion.FiniteHeightContinuity`): at every height some pair of the
tower is still separated. -/
def UnboundedDepth (B : ℕ → TopCat.{u}) (b t : (n : ℕ) → B n) : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, etaIter k (B n) (b n) ≠ etaIter k (B n) (t n)

/-- Separation of the `n`-th pair at height `n` gives unbounded depth. -/
theorem unboundedDepth_of_separated (B : ℕ → TopCat.{u}) (b t : (n : ℕ) → B n)
    (hsep : ∀ n, etaIter n (B n) (b n) ≠ etaIter n (B n) (t n)) : UnboundedDepth B b t :=
  fun k => ⟨k, hsep k⟩

/-- The separator under the weaker unbounded-depth hypothesis. -/
theorem not_finiteHeight_pi_of_unboundedDepth (B : ℕ → TopCat.{u}) (b t : (n : ℕ) → B n)
    (hud : UnboundedDepth B b t) : ¬ FiniteHeight (towerProduct B) b t := by
  rintro ⟨m, hm⟩
  obtain ⟨n, hn⟩ := hud m
  let π : C(towerProduct B, B n) := ⟨fun x => x n, continuous_apply n⟩
  exact hn (etaIter_map_eq π hm)

theorem fhClass_ne_of_unboundedDepth (B : ℕ → TopCat.{u}) (b t : (n : ℕ) → B n)
    (hud : UnboundedDepth B b t) :
    fhClass (X := towerProduct B) b ≠ fhClass (X := towerProduct B) t :=
  fun h => not_finiteHeight_pi_of_unboundedDepth B b t hud (fhClass_eq_iff.mp h)

section Sections

variable {U T : TopCat.{u}}

/-- The class assigned to a continuous map out of a space of pairwise finite
height: the class of the image of any point. -/
def sectionClass (u₀ : U) (f : C(U, T)) : FHQuot T := fhClass (f u₀)

theorem sectionClass_eq (hU : PairwiseFiniteHeight U) (u₀ u : U) (f : C(U, T)) :
    sectionClass u₀ f = fhClass (f u) :=
  fhClass_eq_iff.mpr ((hU u₀ u).map f)

theorem sectionClass_indep (hU : PairwiseFiniteHeight U) (u₀ u₁ : U) (f : C(U, T)) :
    sectionClass u₀ f = sectionClass u₁ f :=
  sectionClass_eq hU u₀ u₁ f

/-- Naturality: restriction along any map of stages preserves the class. -/
theorem sectionClass_comp {V : TopCat.{u}} (hU : PairwiseFiniteHeight U) (v₀ : V) (u₀ : U)
    (g : C(V, U)) (f : C(U, T)) :
    sectionClass v₀ (f.comp g) = sectionClass u₀ f :=
  (sectionClass_eq hU u₀ (g v₀) f).symm

end Sections

end RealContinuity
