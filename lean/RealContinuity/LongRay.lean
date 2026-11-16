import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Order.WithBot
import Mathlib.Data.Prod.Lex
import Mathlib.Topology.Connected.PathConnected

/-!
# The closed long ray

`L = ω₁ ×ₗ [0, 1)` with one added last point `∞ = ⊤`, in its order topology.
`W = ω₁.ToType` is the well-order of countable ordinals.

This file proves the facts about `L` that do not need real charts:

* every countable set of countable ordinals has a strict upper bound;
* hence every countable set of finite points of `L` is bounded by a finite point;
* no path joins a finite point to `∞`: a path is either constant at `∞`
  or has image below some finite point.

The argument for the last fact uses only density of a countable subset of
the (separable) image, not hereditary separability.
-/

noncomputable section

open Set Topology Ordinal

namespace RealContinuity

/-- Countable ordinals, as a type in `Type`. -/
abbrev W : Type := (ω₁ : Ordinal.{0}).ToType

/-- The finite part of the long ray. -/
abbrev L₀ : Type := W ×ₗ Ico (0 : ℝ) 1

/-- The closed long ray. -/
abbrev L : Type := WithTop L₀

instance : TopologicalSpace L := Preorder.topology L

instance : OrderTopology L := ⟨rfl⟩

/-! ### Countable boundedness -/

/-- Every countable set of countable ordinals has a strict upper bound. -/
theorem W.exists_gt_of_countable {S : Set W} (hS : S.Countable) : ∃ b : W, ∀ s ∈ S, s < b := by
  have hc : Countable S := hS.to_subtype
  let f : S → Ordinal.{0} := fun s => ((ToType.mk.symm (s : W) : Iio ω₁) : Ordinal)
  have hf : ∀ s, f s < ω₁ := fun s => (ToType.mk.symm (s : W)).2
  have hsup : (⨆ s, f s) < ω₁ := Ordinal.iSup_lt_omega_one hf
  have hsucc : (⨆ s, f s) + 1 < ω₁ := (Cardinal.isSuccLimit_omega 1).add_one_lt hsup
  refine ⟨ToType.mk ⟨(⨆ s, f s) + 1, hsucc⟩, fun s hs => ?_⟩
  have hle : f ⟨s, hs⟩ ≤ ⨆ s, f s := Ordinal.le_iSup f ⟨s, hs⟩
  have hlt : ToType.mk.symm s < (⟨(⨆ s, f s) + 1, hsucc⟩ : Iio ω₁) := by
    change f ⟨s, hs⟩ < (⨆ s, f s) + 1
    exact lt_of_le_of_lt hle (Order.lt_add_one_iff.mpr le_rfl)
  simpa using ToType.mk.lt_iff_lt.mpr hlt

instance : Nonempty W :=
  ⟨(W.exists_gt_of_countable (Set.countable_empty : (∅ : Set W).Countable)).choose⟩

theorem W.exists_gt (a : W) : ∃ b : W, a < b := by
  obtain ⟨b, hb⟩ := W.exists_gt_of_countable (Set.countable_singleton a)
  exact ⟨b, hb a rfl⟩

/-- The ordinal point `(b, 0)` of the long ray. -/
def ordPt (b : W) : L := ((toLex (b, ⟨0, le_rfl, zero_lt_one⟩) : L₀) : L)

theorem coe_lt_top (x : L₀) : (x : L) < ⊤ := WithTop.coe_lt_top x

theorem ordPt_lt_ordPt {b b' : W} (h : b < b') : ordPt b < ordPt b' := by
  simp only [ordPt, WithTop.coe_lt_coe]
  exact Prod.Lex.lt_iff.mpr (Or.inl h)

theorem coe_lt_ordPt {s : L₀} {b : W} (h : (ofLex s).1 < b) : (s : L) < ordPt b := by
  simp only [ordPt, WithTop.coe_lt_coe]
  exact Prod.Lex.lt_iff.mpr (Or.inl h)

/-- Every countable set of finite points lies below some ordinal point. -/
theorem exists_ordPt_gt_of_countable {S : Set L₀} (hS : S.Countable) :
    ∃ b : W, ∀ s ∈ S, (s : L) < ordPt b := by
  obtain ⟨b, hb⟩ := W.exists_gt_of_countable (hS.image fun x => (ofLex x).1)
  refine ⟨b, fun s hs => ?_⟩
  exact coe_lt_ordPt (hb _ ⟨s, hs, rfl⟩)

/-- Above every finite point there is an ordinal point (in particular a finite
point strictly below `∞`). -/
theorem exists_ordPt_gt (x : L₀) : ∃ b : W, (x : L) < ordPt b :=
  let ⟨b, hb⟩ := exists_ordPt_gt_of_countable (Set.countable_singleton x)
  ⟨b, hb x rfl⟩

theorem ordPt_lt_top (b : W) : ordPt b < ⊤ := coe_lt_top _

instance : Nontrivial L :=
  ⟨⟨ordPt (Classical.arbitrary W), ⊤, (ordPt_lt_top _).ne⟩⟩

theorem ordPt_le_ordPt {b b' : W} (h : b ≤ b') : ordPt b ≤ ordPt b' := by
  rcases eq_or_lt_of_le h with h | h
  · rw [h]
  · exact (ordPt_lt_ordPt h).le

/-! ### No path from a finite point to `∞` -/

/-- A separable preconnected subset of `L` containing `∞` contains no finite
point. -/
theorem no_finite_of_separable_preconnected {K : Set L} (hK : IsPreconnected K)
    (hs : TopologicalSpace.IsSeparable K) (htop : (⊤ : L) ∈ K) :
    ∀ x : L₀, (x : L) ∉ K := by
  intro x hx
  obtain ⟨D, hDc, hKD⟩ := hs
  -- the finite points of the countable set `D` are bounded by an ordinal point
  let D₀ : Set L₀ := {y | (y : L) ∈ D}
  have hD₀ : D₀.Countable := by
    have : D₀ = WithTop.some ⁻¹' D := rfl
    rw [this]
    exact hDc.preimage (WithTop.coe_injective)
  obtain ⟨b, hb⟩ := exists_ordPt_gt_of_countable (hD₀.union (Set.countable_singleton x))
  obtain ⟨b', hb'⟩ := W.exists_gt b
  -- the open interval `(ordPt b, ⊤)` meets `K` but not `D`
  have hlt : ordPt b < ordPt b' := ordPt_lt_ordPt hb'
  have hxb : (x : L) < ordPt b := hb x (Or.inr rfl)
  have hmem : ordPt b' ∈ K := hK.Icc_subset hx htop ⟨(hxb.trans hlt).le, le_top⟩
  have hopen : IsOpen (Ioo (ordPt b) ⊤) := isOpen_Ioo
  have hcl : ordPt b' ∈ closure D := hKD hmem
  obtain ⟨d, hdU, hdD⟩ := mem_closure_iff.mp hcl _ hopen ⟨hlt, ordPt_lt_top b'⟩
  -- `d` is finite (it is below `⊤`) and lies in `D`, so it is below `ordPt b`
  obtain ⟨y, rfl⟩ : ∃ y : L₀, (y : L) = d := WithTop.ne_top_iff_exists.mp (ne_of_lt hdU.2)
  exact lt_asymm hdU.1 (hb y (Or.inl hdD))

/-- No path joins a finite point to `∞`. -/
theorem not_joined_finite_top (x : L₀) : ¬ Joined (x : L) ⊤ := by
  rintro ⟨γ⟩
  have hK : IsPreconnected (range γ) := isPreconnected_range γ.continuous
  have hs : TopologicalSpace.IsSeparable (range γ) :=
    (TopologicalSpace.isSeparable_univ_iff.mpr inferInstance).image γ.continuous |>.mono
      (by rintro _ ⟨t, rfl⟩; exact ⟨t, trivial, rfl⟩)
  exact no_finite_of_separable_preconnected hK hs ⟨1, γ.target⟩ x ⟨0, γ.source⟩

/-- Every path in `L` is constant at `∞` or stays below an ordinal point. -/
theorem path_const_top_or_bounded (γ : C(unitInterval, L)) :
    (∀ t, γ t = ⊤) ∨ ∃ b : W, ∀ t, γ t < ordPt b := by
  by_cases h : ∃ t, γ t = ⊤
  · left
    obtain ⟨t₀, ht₀⟩ := h
    intro t
    by_contra hne
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp hne
    have hK : IsPreconnected (range γ) := isPreconnected_range γ.continuous
    have hs : TopologicalSpace.IsSeparable (range γ) :=
      (TopologicalSpace.isSeparable_univ_iff.mpr inferInstance).image γ.continuous |>.mono
        (by rintro _ ⟨t, rfl⟩; exact ⟨t, trivial, rfl⟩)
    exact no_finite_of_separable_preconnected hK hs ⟨t₀, ht₀⟩ y ⟨t, hy.symm⟩
  · right
    push Not at h
    -- the image is separable; a countable dense subset is bounded, hence so is its closure
    have hs : TopologicalSpace.IsSeparable (range γ) :=
      (TopologicalSpace.isSeparable_univ_iff.mpr inferInstance).image γ.continuous |>.mono
        (by rintro _ ⟨t, rfl⟩; exact ⟨t, trivial, rfl⟩)
    obtain ⟨D, hDc, hKD⟩ := hs
    let D₀ : Set L₀ := {y | (y : L) ∈ D}
    have hD₀ : D₀.Countable := hDc.preimage WithTop.coe_injective
    obtain ⟨b, hb⟩ := exists_ordPt_gt_of_countable hD₀
    obtain ⟨b', hb'⟩ := W.exists_gt b
    have hlt : ordPt b < ordPt b' := ordPt_lt_ordPt hb'
    refine ⟨b', fun t => ?_⟩
    have hDsub : D ⊆ Iic (ordPt b) ∪ {⊤} := by
      intro d hd
      induction d using WithTop.recTopCoe with
      | top => exact Or.inr rfl
      | coe y => exact Or.inl (hb y hd).le
    have hclosed : IsClosed (Iic (ordPt b) ∪ {(⊤ : L)}) := isClosed_Iic.union isClosed_singleton
    have hmem := closure_minimal hDsub hclosed (hKD ⟨t, rfl⟩)
    rcases hmem with hle | htop
    · exact lt_of_le_of_lt hle hlt
    · exact absurd htop (h t)

end RealContinuity
