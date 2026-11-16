import RealContinuity.PathQuotient
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Constructions

/-!
# Finite `Q`-height

Two points of a space have finite `Q`-height when their images in some
iterate `Q^m X` agree. This file proves the generic facts used in §7 of the
countermodel: finite height is an equivalence relation preserved by continuous
maps; open surjections with path-connected fibres raise heights by one; finite
products and connected spaces with locally finite height inherit pairwise
finite height; and a dense path-connected subset bounds all heights by two.
-/

noncomputable section

open Topology Set

namespace RealContinuity

universe u

/-- `x` and `y` have equal images in some finite iterate of `Q`. -/
def FiniteHeight (X : TopCat.{u}) (x y : X) : Prop :=
  ∃ m : ℕ, etaIter m X x = etaIter m X y

namespace FiniteHeight

variable {X Y : TopCat.{u}}

theorem refl (x : X) : FiniteHeight X x x := ⟨0, rfl⟩

theorem symm {x y : X} (h : FiniteHeight X x y) : FiniteHeight X y x :=
  let ⟨m, hm⟩ := h; ⟨m, hm.symm⟩

theorem trans {x y z : X} (h₁ : FiniteHeight X x y) (h₂ : FiniteHeight X y z) :
    FiniteHeight X x z := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  exact ⟨max m n, (etaIter_eq_of_le (le_max_left m n) hm).trans
    (etaIter_eq_of_le (le_max_right m n) hn)⟩

theorem map (f : C(X, Y)) {x y : X} (h : FiniteHeight X x y) : FiniteHeight Y (f x) (f y) :=
  let ⟨m, hm⟩ := h; ⟨m, etaIter_map_eq f hm⟩

theorem of_joined {x y : X} (h : Joined x y) : FiniteHeight X x y :=
  ⟨1, by
    change etaIter 0 (Q X) (eta X x) = etaIter 0 (Q X) (eta X y)
    exact eta_eq_of_joined h⟩

end FiniteHeight

/-- Finite height as a setoid. -/
def finiteHeightSetoid (X : TopCat.{u}) : Setoid X where
  r := FiniteHeight X
  iseqv := ⟨FiniteHeight.refl, FiniteHeight.symm, FiniteHeight.trans⟩

/-- Every pair of points has finite height. -/
def PairwiseFiniteHeight (X : TopCat.{u}) : Prop := ∀ x y : X, FiniteHeight X x y

/-- Pairwise finite height transfers along continuous surjections. -/
theorem PairwiseFiniteHeight.of_surjective {X Y : TopCat.{u}} (f : C(X, Y))
    (hf : Function.Surjective f) (hX : PairwiseFiniteHeight X) : PairwiseFiniteHeight Y := by
  intro y y'
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨x', rfl⟩ := hf y'
  exact (hX x x').map f

/-- Pairwise finite height transfers along homeomorphisms. -/
theorem PairwiseFiniteHeight.of_homeomorph {X Y : TopCat.{u}} (e : X ≃ₜ Y)
    (hX : PairwiseFiniteHeight X) : PairwiseFiniteHeight Y :=
  hX.of_surjective (e : C(X, Y)) e.surjective

section OpenSurjection

variable {B U : TopCat.{u}} (p : C(B, U)) (hopen : IsOpenMap p)
  (hsurj : Function.Surjective p)
  (hfib : ∀ ⦃b b' : B⦄, p b = p b' → Joined b b')
include hopen hsurj hfib

/-- An open surjection with path-connected fibres induces `s : U → Q B` with
`s ∘ p = η_B`. -/
theorem exists_section_of_openSurjection :
    ∃ s : C(U, Q B), ∀ b, s (p b) = eta B b := by
  classical
  have hq : IsQuotientMap p := hopen.isQuotientMap p.continuous hsurj
  let s₀ : U → Q B := fun u => eta B (Classical.choose (hsurj u))
  have hs₀ : ∀ b, s₀ (p b) = eta B b := by
    intro b
    apply eta_eq_of_joined
    apply hfib
    exact Classical.choose_spec (hsurj (p b))
  have hcont : Continuous s₀ := by
    rw [hq.continuous_iff]
    have : s₀ ∘ p = eta B := funext hs₀
    rw [this]
    exact (eta B).continuous
  exact ⟨⟨s₀, hcont⟩, hs₀⟩

/-- Equality of base points at height `m` gives equality of arbitrary lifts at
height `m + 1`. -/
theorem etaIter_succ_eq_of_openSurjection {m : ℕ} {b b' : B}
    (h : etaIter m U (p b) = etaIter m U (p b')) :
    etaIter (m + 1) B b = etaIter (m + 1) B b' := by
  obtain ⟨s, hs⟩ := exists_section_of_openSurjection p hopen hsurj hfib
  change etaIter m (Q B) (eta B b) = etaIter m (Q B) (eta B b')
  rw [← hs b, ← hs b']
  exact etaIter_map_eq s h

/-- Finite height lifts along open surjections with path-connected fibres. -/
theorem FiniteHeight.of_openSurjection {b b' : B} (h : FiniteHeight U (p b) (p b')) :
    FiniteHeight B b b' :=
  let ⟨m, hm⟩ := h
  ⟨m + 1, etaIter_succ_eq_of_openSurjection p hopen hsurj hfib hm⟩

theorem PairwiseFiniteHeight.of_openSurjection (hU : PairwiseFiniteHeight U) :
    PairwiseFiniteHeight B :=
  fun _ _ => FiniteHeight.of_openSurjection p hopen hsurj hfib (hU _ _)

end OpenSurjection

/-- Finite products preserve pairwise finite height, without assuming that `Q`
preserves products: change one coordinate at a time. -/
theorem PairwiseFiniteHeight.prod {X Y : TopCat.{u}} (hX : PairwiseFiniteHeight X)
    (hY : PairwiseFiniteHeight Y) : PairwiseFiniteHeight (TopCat.of (X × Y)) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩
  let i : C(X, TopCat.of (X × Y)) := ⟨fun a => (a, y), by fun_prop⟩
  let j : C(Y, TopCat.of (X × Y)) := ⟨fun c => (x', c), by fun_prop⟩
  exact ((hX x x').map i).trans ((hY y y').map j)

/-- Local-to-global: on a preconnected space, if every point has a
neighbourhood of points at finite height from it, all pairs have finite
height. The classes of the finite-height relation are clopen. -/
theorem PairwiseFiniteHeight.of_locally {X : TopCat.{u}} [PreconnectedSpace X]
    (h : ∀ x : X, ∃ V ∈ 𝓝 x, ∀ y ∈ V, FiniteHeight X x y) : PairwiseFiniteHeight X := by
  intro x₀ y₀
  let S : Set X := {y | FiniteHeight X x₀ y}
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨V, hV, hVy⟩ := h y
    exact Filter.mem_of_superset hV fun z hz => FiniteHeight.trans hy (hVy z hz)
  have hS_closed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨V, hV, hVy⟩ := h y
    refine Filter.mem_of_superset hV fun z hz hzS => hy ?_
    exact FiniteHeight.trans hzS (hVy z hz).symm
  have hS : S = univ := (isClopen_iff.mp ⟨hS_closed, hS_open⟩).resolve_left
    (Set.nonempty_iff_ne_empty.mp ⟨x₀, FiniteHeight.refl x₀⟩)
  have : y₀ ∈ S := hS ▸ mem_univ y₀
  exact this

/-- A preconnected space covered by open subspaces of pairwise finite height
has pairwise finite height. -/
theorem PairwiseFiniteHeight.of_openCover {X : TopCat.{u}} [PreconnectedSpace X]
    (h : ∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ PairwiseFiniteHeight (TopCat.of V)) :
    PairwiseFiniteHeight X := by
  apply PairwiseFiniteHeight.of_locally
  intro x
  obtain ⟨V, hVo, hxV, hV⟩ := h x
  refine ⟨V, hVo.mem_nhds hxV, fun y hy => ?_⟩
  let i : C(TopCat.of V, X) := ⟨Subtype.val, continuous_subtype_val⟩
  exact (hV ⟨x, hxV⟩ ⟨y, hy⟩).map i

/-- A point whose closure is everything is joined to every point by a path. -/
theorem joined_of_dense_point {Y : Type u} [TopologicalSpace Y] {d : Y}
    (hd : ∀ V : Set Y, IsOpen V → V.Nonempty → d ∈ V) (y : Y) : Joined d y := by
  classical
  let γ : unitInterval → Y := fun t => if (t : ℝ) = 1 then y else d
  have hγ : Continuous γ := by
    rw [continuous_def]
    intro V hV
    by_cases hyV : y ∈ V
    · have hdV : d ∈ V := hd V hV ⟨y, hyV⟩
      have : γ ⁻¹' V = univ := by
        ext t; simp only [γ, mem_preimage, mem_univ, iff_true]; split_ifs <;> assumption
      rw [this]; exact isOpen_univ
    · by_cases hdV : d ∈ V
      · have : γ ⁻¹' V = {t : unitInterval | (t : ℝ) ≠ 1} := by
          ext t
          change γ t ∈ V ↔ (t : ℝ) ≠ 1
          simp only [γ]
          split_ifs with ht
          · simp [ht, hyV]
          · simp [ht, hdV]
        rw [this]
        exact isOpen_ne_fun continuous_subtype_val continuous_const
      · have : γ ⁻¹' V = ∅ := by
          ext t; simp only [γ, mem_preimage, mem_empty_iff_false, iff_false]
          split_ifs <;> assumption
        rw [this]; exact isOpen_empty
  exact ⟨{ toFun := γ, continuous_toFun := hγ,
           source' := by simp [γ], target' := by simp [γ] }⟩

/-- A dense path-connected subset forces every pair of points to agree at
height two. -/
theorem etaIter_two_eq_of_dense {X : TopCat.{u}} {F : Set X} (hF : Dense F)
    (hpc : IsPathConnected F) (x y : X) : etaIter 2 X x = etaIter 2 X y := by
  obtain ⟨f₀, hf₀⟩ := hpc.nonempty
  set d : Q X := eta X f₀
  -- every nonempty open set of `Q X` contains `d`
  have hd : ∀ V : Set (Q X), IsOpen V → V.Nonempty → d ∈ V := by
    intro V hV hne
    have hpre : IsOpen (eta X ⁻¹' V) := hV.preimage (eta X).continuous
    have hpne : (eta X ⁻¹' V).Nonempty := by
      obtain ⟨z, hz⟩ := hne
      obtain ⟨x', rfl⟩ := eta_surjective X z
      exact ⟨x', hz⟩
    obtain ⟨f, hfV, hfF⟩ := hF.inter_open_nonempty _ hpre hpne
    have : eta X f = d := eta_eq_of_joined ((hpc.joinedIn f hfF f₀ hf₀).joined)
    rw [← this]; exact hfV
  change etaIter 1 (Q X) (eta X x) = etaIter 1 (Q X) (eta X y)
  change etaIter 0 (Q (Q X)) (eta (Q X) (eta X x)) = etaIter 0 (Q (Q X)) (eta (Q X) (eta X y))
  exact (eta_eq_of_joined (joined_of_dense_point hd _)).symm.trans
    (eta_eq_of_joined (joined_of_dense_point hd _))

theorem PairwiseFiniteHeight.of_dense {X : TopCat.{u}} {F : Set X} (hF : Dense F)
    (hpc : IsPathConnected F) : PairwiseFiniteHeight X :=
  fun x y => ⟨2, etaIter_two_eq_of_dense hF hpc x y⟩

end RealContinuity
