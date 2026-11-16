import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.ProjIcc

/-!
# A global relative homotopy for paths in a linearly ordered space

Let `T` be a linearly ordered space with its order topology (for instance the
closed long ray or one of its tails). For two paths `p₀ p₁ : I → T` with
the same endpoints we construct, using only maxima and minima over compact
sets, a homotopy `p₀ ≃ p₁` relative to the endpoints which depends jointly
continuously on the pair of paths and the homotopy parameter.

The construction descends from `p₀` to `m = min p₀ p₁` and then ascends to
`p₁`:
`H₁(u, τ) = max (m τ) (min (p₀ τ) (c u))`, where the control value `c` runs
from `max p₀` down to `min m` through running maxima of `p₀` and running
minima of `m`. Every value of the homotopy at `τ` lies between
`min (p₀ τ) (p₁ τ)` and `max (p₀ τ) (p₁ τ)`; hence the homotopy stays in every
tail, in every order-convex chart, and in every uniform chart ball that
contains both paths.

This order-theoretic homotopy replaces the cap–min extension `E₂` of the
proof draft for the kernel pair of the endpoint map (approved by Colin,
25 October 2026: the required result is the relative homotopy). It has the
properties the descent argument uses: `H(p₀,p₁,0) = p₀`, `H(p₀,p₁,1) = p₁`,
joint continuity in the pair and the parameter on the compact-open path
space, preservation of every parameter where the paths agree (in particular
the common endpoints, so it is a homotopy over `K_T` and survives base
change), and preservation of the designated restricted domains: tails (via
`relHomotopy_mem_of_ordConnected`, or by instantiating `T` with the tail
itself, whose subspace topology is its order topology) and uniform balls of
monotone charts (`BottomChart.relHomotopy_mem_V`). Pointwise bounds do NOT
preserve arbitrary convex subsets of a function space; only these specific
domains are claimed.
-/

noncomputable section

open Set Topology unitInterval

namespace RealContinuity

namespace OrderHomotopy

variable {T : Type*} [TopologicalSpace T] [LinearOrder T] [OrderTopology T]

/-! ### Maxima and minima of paths -/

/-- The maximum value of a path (it is attained). -/
def pathMax (f : C(I, T)) : T :=
  Classical.choose ((isCompact_range f.continuous).exists_isGreatest (range_nonempty f))

/-- The minimum value of a path (it is attained). -/
def pathMin (f : C(I, T)) : T :=
  Classical.choose ((isCompact_range f.continuous).exists_isLeast (range_nonempty f))

theorem pathMax_isGreatest (f : C(I, T)) : IsGreatest (range f) (pathMax f) :=
  Classical.choose_spec ((isCompact_range f.continuous).exists_isGreatest (range_nonempty f))

theorem pathMin_isLeast (f : C(I, T)) : IsLeast (range f) (pathMin f) :=
  Classical.choose_spec ((isCompact_range f.continuous).exists_isLeast (range_nonempty f))

theorem le_pathMax (f : C(I, T)) (t : I) : f t ≤ pathMax f :=
  (pathMax_isGreatest f).2 ⟨t, rfl⟩

theorem pathMin_le (f : C(I, T)) (t : I) : pathMin f ≤ f t :=
  (pathMin_isLeast f).2 ⟨t, rfl⟩

theorem exists_eq_pathMax (f : C(I, T)) : ∃ t, f t = pathMax f := (pathMax_isGreatest f).1

theorem exists_eq_pathMin (f : C(I, T)) : ∃ t, f t = pathMin f := (pathMin_isLeast f).1

theorem lt_pathMax_iff {f : C(I, T)} {a : T} : a < pathMax f ↔ ∃ t, a < f t := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := exists_eq_pathMax f
    exact ⟨t, ht ▸ h⟩
  · rintro ⟨t, ht⟩
    exact ht.trans_le (le_pathMax f t)

theorem pathMax_lt_iff {f : C(I, T)} {b : T} : pathMax f < b ↔ ∀ t, f t < b := by
  constructor
  · intro h t
    exact (le_pathMax f t).trans_lt h
  · intro h
    obtain ⟨t, ht⟩ := exists_eq_pathMax f
    exact ht ▸ h t

theorem pathMin_lt_iff {f : C(I, T)} {b : T} : pathMin f < b ↔ ∃ t, f t < b := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := exists_eq_pathMin f
    exact ⟨t, ht ▸ h⟩
  · rintro ⟨t, ht⟩
    exact (pathMin_le f t).trans_lt ht

theorem lt_pathMin_iff {f : C(I, T)} {a : T} : a < pathMin f ↔ ∀ t, a < f t := by
  constructor
  · intro h t
    exact h.trans_le (pathMin_le f t)
  · intro h
    obtain ⟨t, ht⟩ := exists_eq_pathMin f
    exact ht ▸ h t

theorem continuous_pathMax : Continuous (pathMax : C(I, T) → T) := by
  rw [OrderTopology.continuous_iff]
  intro a
  constructor
  · have : pathMax ⁻¹' Ioi a = ⋃ t : I, {f : C(I, T) | a < f t} := by
      ext f; simp [lt_pathMax_iff]
    rw [this]
    exact isOpen_iUnion fun t => isOpen_lt continuous_const (continuous_eval_const t)
  · have : pathMax ⁻¹' Iio a = {f : C(I, T) | MapsTo f univ (Iio a)} := by
      ext f; simp [pathMax_lt_iff, MapsTo]
    rw [this]
    exact ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ isOpen_Iio

theorem continuous_pathMin : Continuous (pathMin : C(I, T) → T) := by
  rw [OrderTopology.continuous_iff]
  intro a
  constructor
  · have : pathMin ⁻¹' Ioi a = {f : C(I, T) | MapsTo f univ (Ioi a)} := by
      ext f; simp [lt_pathMin_iff, MapsTo]
    rw [this]
    exact ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ isOpen_Ioi
  · have : pathMin ⁻¹' Iio a = ⋃ t : I, {f : C(I, T) | f t < a} := by
      ext f; simp [pathMin_lt_iff]
    rw [this]
    exact isOpen_iUnion fun t => isOpen_lt (continuous_eval_const t) continuous_const

/-! ### Running maxima and minima -/

/-- `(s, σ) ↦ s σ` on the unit interval. -/
def scale : C(I × I, I) := ⟨fun x => ⟨x.1 * x.2, mul_mem x.1.2 x.2.2⟩, by fun_prop⟩

/-- Restriction of a path to `[0, s]`, reparametrized by `I`. -/
def restrictTo (f : C(I, T)) (s : I) : C(I, T) := f.comp (scale.curry s)

theorem continuous_restrictTo :
    Continuous fun x : C(I, T) × I => restrictTo x.1 x.2 :=
  ContinuousMap.continuous_comp'.comp
    ((scale.curry.continuous.comp continuous_snd).prodMk continuous_fst)

/-- The maximum of `f` on `[0, s]`. -/
def runningMax (f : C(I, T)) (s : I) : T := pathMax (restrictTo f s)

/-- The minimum of `f` on `[0, s]`. -/
def runningMin (f : C(I, T)) (s : I) : T := pathMin (restrictTo f s)

theorem continuous_runningMax : Continuous fun x : C(I, T) × I => runningMax x.1 x.2 :=
  continuous_pathMax.comp continuous_restrictTo

theorem continuous_runningMin : Continuous fun x : C(I, T) × I => runningMin x.1 x.2 :=
  continuous_pathMin.comp continuous_restrictTo

omit [LinearOrder T] [OrderTopology T] in
theorem restrictTo_zero_apply (f : C(I, T)) (t : I) : restrictTo f 0 t = f 0 := by
  simp only [restrictTo, ContinuousMap.comp_apply, ContinuousMap.curry_apply, scale,
    ContinuousMap.coe_mk]
  congr 1
  ext
  simp

omit [LinearOrder T] [OrderTopology T] in
theorem restrictTo_one (f : C(I, T)) : restrictTo f 1 = f := by
  ext t
  simp only [restrictTo, ContinuousMap.comp_apply, ContinuousMap.curry_apply, scale,
    ContinuousMap.coe_mk]
  congr 1
  ext
  simp

theorem runningMax_zero (f : C(I, T)) : runningMax f 0 = f 0 := by
  obtain ⟨t, ht⟩ := exists_eq_pathMax (restrictTo f 0)
  rw [runningMax, ← ht, restrictTo_zero_apply]

theorem runningMin_zero (f : C(I, T)) : runningMin f 0 = f 0 := by
  obtain ⟨t, ht⟩ := exists_eq_pathMin (restrictTo f 0)
  rw [runningMin, ← ht, restrictTo_zero_apply]

theorem runningMax_one (f : C(I, T)) : runningMax f 1 = pathMax f := by
  rw [runningMax, restrictTo_one]

theorem runningMin_one (f : C(I, T)) : runningMin f 1 = pathMin f := by
  rw [runningMin, restrictTo_one]

theorem exists_eq_runningMax (f : C(I, T)) (s : I) : ∃ t, f t = runningMax f s := by
  obtain ⟨t, ht⟩ := exists_eq_pathMax (restrictTo f s)
  exact ⟨_, ht⟩

theorem exists_eq_runningMin (f : C(I, T)) (s : I) : ∃ t, f t = runningMin f s := by
  obtain ⟨t, ht⟩ := exists_eq_pathMin (restrictTo f s)
  exact ⟨_, ht⟩

/-! ### The homotopy -/

/-- The pointwise minimum of two paths. -/
def lowerPath (p₀ p₁ : C(I, T)) : C(I, T) :=
  ⟨fun τ => min (p₀ τ) (p₁ τ), p₀.continuous.min p₁.continuous⟩

/-- Clamp a real number to the unit interval. -/
abbrev clampI (x : ℝ) : I := projIcc 0 1 zero_le_one x

/-- The control value: from `max p₀` down to `p₀ 0` (running maxima of `p₀`),
then down to `min m` (running minima of `m = min p₀ p₁`). -/
def control (p₀ p₁ : C(I, T)) (s : I) : T :=
  if (s : ℝ) ≤ 1 / 2 then runningMax p₀ (clampI (1 - 2 * s))
  else runningMin (lowerPath p₀ p₁) (clampI (2 * s - 1))

/-- The descending half: from `p₀` (at `u = 0`) to `min p₀ p₁` (at `u = 1`). -/
def descend (p₀ p₁ : C(I, T)) (u τ : I) : T :=
  max (min (p₀ τ) (p₁ τ)) (min (p₀ τ) (control p₀ p₁ u))

/-- The homotopy from `p₀` to `p₁`. -/
def relHom (p₀ p₁ : C(I, T)) (u τ : I) : T :=
  if (u : ℝ) ≤ 1 / 2 then descend p₀ p₁ (clampI (2 * u)) τ
  else descend p₁ p₀ (clampI (2 - 2 * u)) τ

theorem control_zero (p₀ p₁ : C(I, T)) : control p₀ p₁ 0 = pathMax p₀ := by
  have h : clampI (1 - 2 * ((0 : I) : ℝ)) = 1 := by
    ext; simp
  simp only [control, Icc.coe_zero, one_div, inv_nonneg, zero_le_two, ↓reduceIte] at *
  rw [show (1 : ℝ) - 2 * 0 = 1 by ring] at h ⊢
  rw [h, runningMax_one]

theorem control_one (p₀ p₁ : C(I, T)) : control p₀ p₁ 1 = pathMin (lowerPath p₀ p₁) := by
  have h : clampI (2 * ((1 : I) : ℝ) - 1) = 1 := by
    ext; simp; norm_num
  have h2 : ¬ ((1 : I) : ℝ) ≤ 1 / 2 := by norm_num
  simp only [control, h2, ↓reduceIte]
  rw [h, runningMin_one]

theorem descend_zero (p₀ p₁ : C(I, T)) (τ : I) : descend p₀ p₁ 0 τ = p₀ τ := by
  rw [descend, control_zero, min_eq_left (le_pathMax p₀ τ)]
  exact max_eq_right (min_le_left _ _)

theorem descend_one (p₀ p₁ : C(I, T)) (τ : I) : descend p₀ p₁ 1 τ = min (p₀ τ) (p₁ τ) := by
  rw [descend, control_one]
  have h1 : pathMin (lowerPath p₀ p₁) ≤ min (p₀ τ) (p₁ τ) := pathMin_le (lowerPath p₀ p₁) τ
  have h2 : min (p₀ τ) (pathMin (lowerPath p₀ p₁)) = pathMin (lowerPath p₀ p₁) :=
    min_eq_right (h1.trans (min_le_left _ _))
  rw [h2]
  exact max_eq_left h1

theorem descend_bounds (p₀ p₁ : C(I, T)) (u τ : I) :
    min (p₀ τ) (p₁ τ) ≤ descend p₀ p₁ u τ ∧ descend p₀ p₁ u τ ≤ p₀ τ :=
  ⟨le_max_left _ _, max_le (min_le_left _ _) (min_le_left _ _)⟩

/-- If the endpoints agree at `τ`, the descending half is constant there. -/
theorem descend_of_eq (p₀ p₁ : C(I, T)) (u τ : I) (h : p₀ τ = p₁ τ) :
    descend p₀ p₁ u τ = p₀ τ := by
  rw [descend, ← h, min_self]
  exact max_eq_left (min_le_left _ _)

theorem relHom_zero (p₀ p₁ : C(I, T)) (τ : I) : relHom p₀ p₁ 0 τ = p₀ τ := by
  have : clampI (2 * ((0 : I) : ℝ)) = 0 := by ext; simp
  simp only [relHom, Icc.coe_zero, one_div, inv_nonneg, zero_le_two, ↓reduceIte] at *
  rw [show (2 : ℝ) * 0 = 0 by ring] at this ⊢
  rw [this, descend_zero]

theorem relHom_one (p₀ p₁ : C(I, T)) (τ : I) : relHom p₀ p₁ 1 τ = p₁ τ := by
  have h2 : ¬ ((1 : I) : ℝ) ≤ 1 / 2 := by norm_num
  have : clampI (2 - 2 * ((1 : I) : ℝ)) = 0 := by ext; simp
  simp only [relHom, h2, ↓reduceIte]
  rw [this, descend_zero]

theorem relHom_of_eq (p₀ p₁ : C(I, T)) (u τ : I) (h : p₀ τ = p₁ τ) :
    relHom p₀ p₁ u τ = p₀ τ := by
  unfold relHom
  split_ifs
  · exact descend_of_eq p₀ p₁ _ τ h
  · rw [descend_of_eq p₁ p₀ _ τ h.symm, h]

theorem relHom_bounds (p₀ p₁ : C(I, T)) (u τ : I) :
    min (p₀ τ) (p₁ τ) ≤ relHom p₀ p₁ u τ ∧ relHom p₀ p₁ u τ ≤ max (p₀ τ) (p₁ τ) := by
  unfold relHom
  split_ifs
  · obtain ⟨h1, h2⟩ := descend_bounds p₀ p₁ (clampI (2 * u)) τ
    exact ⟨h1, h2.trans (le_max_left _ _)⟩
  · obtain ⟨h1, h2⟩ := descend_bounds p₁ p₀ (clampI (2 - 2 * u)) τ
    exact ⟨(min_comm (p₀ τ) (p₁ τ)).le.trans h1, h2.trans (le_max_right _ _)⟩

/-! ### Joint continuity on pairs with a common initial point -/

/-- Pairs of paths with the same initial point. -/
def SameStart : Set (C(I, T) × C(I, T)) := {q | q.1 0 = q.2 0}

theorem continuous_lowerPath :
    Continuous fun q : C(I, T) × C(I, T) => lowerPath q.1 q.2 := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)).min
    (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)))

theorem continuous_clampI : Continuous clampI :=
  continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)

theorem continuous_control :
    Continuous fun x : SameStart (T := T) × I => control x.1.1.1 x.1.1.2 x.2 := by
  have hs : Continuous fun x : SameStart (T := T) × I => ((x.2 : I) : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hq : Continuous fun x : SameStart (T := T) × I => (x.1 : C(I, T) × C(I, T)) :=
    continuous_subtype_val.comp continuous_fst
  have hA : Continuous fun x : SameStart (T := T) × I =>
      runningMax x.1.1.1 (clampI (1 - 2 * (x.2 : ℝ))) :=
    continuous_runningMax.comp ((continuous_fst.comp hq).prodMk
      (continuous_clampI.comp (continuous_const.sub (continuous_const.mul hs))))
  have hB : Continuous fun x : SameStart (T := T) × I =>
      runningMin (lowerPath x.1.1.1 x.1.1.2) (clampI (2 * (x.2 : ℝ) - 1)) :=
    continuous_runningMin.comp ((continuous_lowerPath.comp hq).prodMk
      (continuous_clampI.comp ((continuous_const.mul hs).sub continuous_const)))
  unfold control
  refine Continuous.if_le hA hB hs continuous_const ?_
  rintro ⟨⟨q, hq'⟩, s⟩ hs'
  simp only at hs' ⊢
  have h1 : clampI (1 - 2 * (s : ℝ)) = 0 := by ext; simp [hs']
  have h2 : clampI (2 * (s : ℝ) - 1) = 0 := by ext; simp [hs']
  rw [h1, h2, runningMax_zero, runningMin_zero]
  simp only [lowerPath, ContinuousMap.coe_mk]
  change q.1 0 = q.2 0 at hq'
  rw [← hq', min_self]

/-- Swapping a pair with a common initial point. -/
def swapSameStart : C(SameStart (T := T), SameStart (T := T)) :=
  ⟨fun q => ⟨(q.1.2, q.1.1), q.2.symm⟩, by fun_prop⟩

theorem continuous_descend : Continuous fun x : (SameStart (T := T) × I) × I =>
    descend x.1.1.1.1 x.1.1.1.2 x.1.2 x.2 := by
  have hq : Continuous fun x : (SameStart (T := T) × I) × I => (x.1.1 : C(I, T) × C(I, T)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have h0 : Continuous fun x : (SameStart (T := T) × I) × I => x.1.1.1.1 x.2 :=
    continuous_eval.comp ((continuous_fst.comp hq).prodMk continuous_snd)
  have h1 : Continuous fun x : (SameStart (T := T) × I) × I => x.1.1.1.2 x.2 :=
    continuous_eval.comp ((continuous_snd.comp hq).prodMk continuous_snd)
  have hc : Continuous fun x : (SameStart (T := T) × I) × I =>
      control x.1.1.1.1 x.1.1.1.2 x.1.2 :=
    continuous_control.comp continuous_fst
  exact (h0.min h1).max (h0.min hc)

theorem continuous_relHom : Continuous fun x : (SameStart (T := T) × I) × I =>
    relHom x.1.1.1.1 x.1.1.1.2 x.1.2 x.2 := by
  have hu : Continuous fun x : (SameStart (T := T) × I) × I => ((x.1.2 : I) : ℝ) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hA : Continuous fun x : (SameStart (T := T) × I) × I =>
      descend x.1.1.1.1 x.1.1.1.2 (clampI (2 * (x.1.2 : ℝ))) x.2 :=
    continuous_descend.comp (((continuous_fst.comp continuous_fst).prodMk
      (continuous_clampI.comp (continuous_const.mul hu))).prodMk continuous_snd)
  have hB : Continuous fun x : (SameStart (T := T) × I) × I =>
      descend x.1.1.1.2 x.1.1.1.1 (clampI (2 - 2 * (x.1.2 : ℝ))) x.2 :=
    continuous_descend.comp ((((swapSameStart.continuous.comp
      (continuous_fst.comp continuous_fst))).prodMk
      (continuous_clampI.comp (continuous_const.sub (continuous_const.mul hu)))).prodMk
      continuous_snd)
  unfold relHom
  refine Continuous.if_le hA hB hu continuous_const ?_
  rintro ⟨⟨q, u⟩, τ⟩ hu'
  simp only at hu' ⊢
  have h1 : clampI (2 * (u : ℝ)) = 1 := by ext; simp [hu']
  have h2 : clampI (2 - 2 * (u : ℝ)) = 1 := by ext; simp [hu']; norm_num
  rw [h1, h2, descend_one, descend_one, min_comm]

/-- **Global relative homotopy.** For pairs of paths with a common initial
point, a homotopy from the first path to the second, jointly continuous in the
pair and the parameter. -/
def relHomotopy : C(SameStart (T := T) × I, C(I, T)) :=
  ContinuousMap.curry ⟨fun x => relHom x.1.1.1.1 x.1.1.1.2 x.1.2 x.2, continuous_relHom⟩

@[simp]
theorem relHomotopy_apply (q : SameStart (T := T)) (u τ : I) :
    relHomotopy (q, u) τ = relHom q.1.1 q.1.2 u τ := rfl

theorem relHomotopy_zero (q : SameStart (T := T)) : relHomotopy (q, 0) = q.1.1 := by
  ext τ; exact relHom_zero _ _ τ

theorem relHomotopy_one (q : SameStart (T := T)) : relHomotopy (q, 1) = q.1.2 := by
  ext τ; exact relHom_one _ _ τ

/-- The homotopy fixes every parameter at which the two paths agree, in
particular common endpoints. -/
theorem relHomotopy_of_eq (q : SameStart (T := T)) (u τ : I) (h : q.1.1 τ = q.1.2 τ) :
    relHomotopy (q, u) τ = q.1.1 τ :=
  relHom_of_eq _ _ u τ h

theorem relHomotopy_bounds (q : SameStart (T := T)) (u τ : I) :
    min (q.1.1 τ) (q.1.2 τ) ≤ relHomotopy (q, u) τ ∧
      relHomotopy (q, u) τ ≤ max (q.1.1 τ) (q.1.2 τ) :=
  relHom_bounds _ _ u τ

/-- Every value of the homotopy lies in each order-convex set containing the
corresponding values of the two paths. -/
theorem relHomotopy_mem_of_ordConnected {S : Set T} (hS : S.OrdConnected)
    (q : SameStart (T := T)) (u τ : I) (h₀ : q.1.1 τ ∈ S) (h₁ : q.1.2 τ ∈ S) :
    relHomotopy (q, u) τ ∈ S := by
  obtain ⟨hl, hu⟩ := relHomotopy_bounds q u τ
  have hmin : min (q.1.1 τ) (q.1.2 τ) ∈ S := by
    rcases min_choice (q.1.1 τ) (q.1.2 τ) with h | h <;> rw [h] <;> assumption
  have hmax : max (q.1.1 τ) (q.1.2 τ) ∈ S := by
    rcases max_choice (q.1.1 τ) (q.1.2 τ) with h | h <;> rw [h] <;> assumption
  exact hS.out hmin hmax ⟨hl, hu⟩

/-! ### The `ℝ`-parametrized version -/

/-- `ℝ → I`, `t ↦ max 0 (min 1 t)`. -/
def clampR : C(ℝ, I) := ⟨clampI, continuous_clampI⟩

theorem clampR_of_nonpos {t : ℝ} (ht : t ≤ 0) : clampR t = 0 := by
  ext; simp [clampR, ht]

theorem clampR_of_one_le {t : ℝ} (ht : 1 ≤ t) : clampR t = 1 := by
  ext; simp [clampR, ht]

/-- The `ℝ`-homotopy obtained by clamping the parameter. -/
def relRHomotopy : C(SameStart (T := T) × ℝ, C(I, T)) :=
  relHomotopy.comp ⟨fun x => (x.1, clampR x.2), by fun_prop⟩

theorem relRHomotopy_zero (q : SameStart (T := T)) : relRHomotopy (q, 0) = q.1.1 := by
  simp only [relRHomotopy, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    clampR_of_nonpos le_rfl, relHomotopy_zero]

theorem relRHomotopy_one (q : SameStart (T := T)) : relRHomotopy (q, 1) = q.1.2 := by
  simp only [relRHomotopy, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    clampR_of_one_le le_rfl, relHomotopy_one]

end OrderHomotopy

end RealContinuity
