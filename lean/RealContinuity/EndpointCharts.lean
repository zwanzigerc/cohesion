import RealContinuity.OrderHomotopy
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

/-!
# Bounded charts and the endpoint map

A *bottom chart* on a space `T` is a global coordinate `Φ : T → ℝ` with
values in `[0, ∞)`, together with a continuous inverse `ψ : [0, β) → T` on
`J = {Φ < β}`. In the closed long ray, the initial segments `[0, (b,0))` give
such charts; every bounded path lies in one of them, and the half-interval
at the first point `0` is built in.

For a path `p` in `J` and `ε > 0` with `max (Φ ∘ p) + ε < β`, put

* `V = {q | ‖Φ ∘ q - Φ ∘ p‖ < ε}` (a uniform chart ball of paths), and
* `W = {(a, b) | |Φ a - Φ (p 0)| < ε, |Φ b - Φ (p 1)| < ε}`.

Then `V` is open, the endpoint map sends `V` ONTO `W` (its actual image), it
has a continuous local section through every point of `V` (so it is open on
`V`), `V` is path connected, and each fibre of `V → W` is path connected.
-/

noncomputable section

open Set Topology unitInterval

namespace RealContinuity

universe u

/-- The endpoint map `r(p) = (p 0, p 1)`. -/
def endpointMap (T : Type u) [TopologicalSpace T] : C(C(I, T), T × T) :=
  ⟨fun q => (q 0, q 1), (continuous_eval_const 0).prodMk (continuous_eval_const 1)⟩

@[simp] theorem endpointMap_apply {T : Type u} [TopologicalSpace T] (q : C(I, T)) :
    endpointMap T q = (q 0, q 1) := rfl

/-- A bounded chart with a closed end at `0`. -/
structure BottomChart (T : Type u) [TopologicalSpace T] where
  /-- The global coordinate. -/
  Φ : C(T, ℝ)
  /-- The length of the chart. -/
  β : ℝ
  /-- The inverse of the coordinate on `[0, β)`. -/
  ψ : C(Ico (0 : ℝ) β, T)
  nonneg : ∀ x, 0 ≤ Φ x
  Φ_ψ : ∀ s, Φ (ψ s) = s
  ψ_Φ : ∀ x (hx : Φ x < β), ψ ⟨Φ x, nonneg x, hx⟩ = x

namespace BottomChart

variable {T : Type u} [TopologicalSpace T] (c : BottomChart T)

/-- The chart domain. -/
def J : Set T := {x | c.Φ x < c.β}

theorem isOpen_J : IsOpen c.J := isOpen_lt c.Φ.continuous continuous_const

/-- Chart coordinates of a path. -/
def coord (q : C(I, T)) : C(I, ℝ) := c.Φ.comp q

theorem continuous_coord : Continuous c.coord := ContinuousMap.continuous_postcomp c.Φ

/-! ### The data of a controlled chart ball -/

variable (p : C(I, T)) (ε : ℝ)

/-- The uniform chart ball of paths around `p`. -/
def V : Set C(I, T) := {q | dist (c.coord q) (c.coord p) < ε}

/-- Its endpoint image. -/
def W : Set (T × T) := {x | |c.Φ x.1 - c.Φ (p 0)| < ε ∧ |c.Φ x.2 - c.Φ (p 1)| < ε}

theorem isOpen_V : IsOpen (c.V p ε) :=
  isOpen_lt (continuous_dist.comp (c.continuous_coord.prodMk continuous_const)) continuous_const

theorem isOpen_W : IsOpen (c.W p ε) := by
  apply IsOpen.inter
  · exact isOpen_lt (continuous_abs.comp ((c.Φ.continuous.comp continuous_fst).sub
      continuous_const)) continuous_const
  · exact isOpen_lt (continuous_abs.comp ((c.Φ.continuous.comp continuous_snd).sub
      continuous_const)) continuous_const

/-- The standing size condition on a chart ball. -/
structure Admissible : Prop where
  pos : 0 < ε
  fits : OrderHomotopy.pathMax (c.coord p) + ε < c.β

variable {c p ε}

/-- The upper clamping level `β' = max (Φ ∘ p) + ε`. -/
def top' (_h : c.Admissible p ε) : ℝ := OrderHomotopy.pathMax (c.coord p) + ε

theorem top'_lt (h : c.Admissible p ε) : top' h < c.β := h.fits

theorem top'_nonneg (h : c.Admissible p ε) : 0 ≤ top' h := by
  have := c.nonneg (p 0)
  have h0 := OrderHomotopy.le_pathMax (c.coord p) 0
  simp only [coord, ContinuousMap.comp_apply] at h0
  unfold top' coord; linarith [h.pos]

/-- Clamp into `[0, β']`, viewed inside `[0, β)`. -/
def clampTo (h : c.Admissible p ε) : C(ℝ, Ico (0 : ℝ) c.β) :=
  ⟨fun x => ⟨projIcc 0 (top' h) (top'_nonneg h) x, (projIcc 0 (top' h) (top'_nonneg h) x).2.1,
      lt_of_le_of_lt (projIcc 0 (top' h) (top'_nonneg h) x).2.2 (top'_lt h)⟩,
    by fun_prop⟩

theorem clampTo_val_of_mem (h : c.Admissible p ε) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ top' h) :
    ((clampTo h x : Ico (0 : ℝ) c.β) : ℝ) = x := by
  simp [clampTo, projIcc, hx0, hx1]

theorem mem_V_iff {q : C(I, T)} (hε : 0 < ε) :
    q ∈ c.V p ε ↔ ∀ τ, |c.Φ (q τ) - c.Φ (p τ)| < ε := by
  change dist (c.coord q) (c.coord p) < ε ↔ _
  rw [ContinuousMap.dist_lt_iff hε]
  simp [coord, Real.dist_eq]

/-- Points of `V` stay inside the clamping range. -/
theorem coord_le_top' (h : c.Admissible p ε) {q : C(I, T)} (hq : q ∈ c.V p ε) (τ : I) :
    c.Φ (q τ) < top' h := by
  have h1 := ((mem_V_iff h.pos).mp hq τ)
  have h2 := OrderHomotopy.le_pathMax (c.coord p) τ
  simp only [coord, ContinuousMap.comp_apply] at h2
  unfold top' coord
  linarith [(abs_lt.mp h1).2]

/-! ### Local sections -/

/-- The linear endpoint correction. -/
def corr (d₀ d₁ : ℝ) (τ : I) : ℝ := (1 - (τ : ℝ)) * d₀ + (τ : ℝ) * d₁

theorem abs_corr_le (d₀ d₁ : ℝ) (τ : I) : |corr d₀ d₁ τ| ≤ max |d₀| |d₁| := by
  have h0 : 0 ≤ (τ : ℝ) := τ.2.1
  have h1 : (τ : ℝ) ≤ 1 := τ.2.2
  unfold corr
  calc |(1 - (τ : ℝ)) * d₀ + (τ : ℝ) * d₁|
      ≤ |(1 - (τ : ℝ)) * d₀| + |(τ : ℝ) * d₁| := abs_add_le _ _
    _ = (1 - (τ : ℝ)) * |d₀| + (τ : ℝ) * |d₁| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg h0]
    _ ≤ (1 - (τ : ℝ)) * max |d₀| |d₁| + (τ : ℝ) * max |d₀| |d₁| :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) h0)
    _ = max |d₀| |d₁| := by ring

/-- The local section through `q`: perturb the chart coordinates of `q` by the
linear endpoint correction, clamp at `0` (and harmlessly at `β'`), and map back. -/
def sect (h : c.Admissible p ε) (q : C(I, T)) : C(T × T, C(I, T)) :=
  ContinuousMap.curry
    ⟨fun x : (T × T) × I => c.ψ (clampTo h (c.Φ (q x.2) +
        corr (c.Φ x.1.1 - c.Φ (q 0)) (c.Φ x.1.2 - c.Φ (q 1)) x.2)),
      by
        unfold corr
        fun_prop⟩

theorem sect_apply (h : c.Admissible p ε) (q : C(I, T)) (x : T × T) (τ : I) :
    c.sect h q x τ = c.ψ (clampTo h (c.Φ (q τ) +
        corr (c.Φ x.1 - c.Φ (q 0)) (c.Φ x.2 - c.Φ (q 1)) τ)) := rfl

/-- The shrinking radius at `q`. -/
def slack (q : C(I, T)) : ℝ := ε - dist (c.coord q) (c.coord p)

/-- The domain of the local section through `q`. -/
def Wq (q : C(I, T)) : Set (T × T) :=
  {x | |c.Φ x.1 - c.Φ (q 0)| < c.slack (p := p) (ε := ε) q ∧
    |c.Φ x.2 - c.Φ (q 1)| < c.slack (p := p) (ε := ε) q}

theorem isOpen_Wq (q : C(I, T)) : IsOpen (c.Wq (p := p) (ε := ε) q) := by
  apply IsOpen.inter
  · exact isOpen_lt (continuous_abs.comp ((c.Φ.continuous.comp continuous_fst).sub
      continuous_const)) continuous_const
  · exact isOpen_lt (continuous_abs.comp ((c.Φ.continuous.comp continuous_snd).sub
      continuous_const)) continuous_const

theorem mem_Wq_self {q : C(I, T)} (hq : q ∈ c.V p ε) :
    endpointMap T q ∈ c.Wq (p := p) (ε := ε) q := by
  have hq' : dist (c.coord q) (c.coord p) < ε := hq
  have : 0 < c.slack (p := p) (ε := ε) q := by
    unfold slack; linarith
  simp [Wq, this]

/-- The perturbed coordinate is within `slack` of the coordinate of `q`. -/
theorem abs_corr_lt_slack {q : C(I, T)} {x : T × T} (hx : x ∈ c.Wq (p := p) (ε := ε) q)
    (τ : I) :
    |corr (c.Φ x.1 - c.Φ (q 0)) (c.Φ x.2 - c.Φ (q 1)) τ| < c.slack (p := p) (ε := ε) q :=
  lt_of_le_of_lt (abs_corr_le _ _ τ) (max_lt hx.1 hx.2)

theorem perturbed_bounds (h : c.Admissible p ε) {q : C(I, T)}
    {x : T × T} (hx : x ∈ c.Wq (p := p) (ε := ε) q) (τ : I) :
    c.Φ (q τ) + corr (c.Φ x.1 - c.Φ (q 0)) (c.Φ x.2 - c.Φ (q 1)) τ ≤ top' h ∧
    |max 0 (c.Φ (q τ) + corr (c.Φ x.1 - c.Φ (q 0)) (c.Φ x.2 - c.Φ (q 1)) τ) - c.Φ (p τ)|
      < ε := by
  have hc := abs_corr_lt_slack hx τ
  have hd : |c.Φ (q τ) - c.Φ (p τ)| ≤ dist (c.coord q) (c.coord p) := by
    have := ContinuousMap.dist_apply_le_dist (f := c.coord q) (g := c.coord p) τ
    simpa [coord, Real.dist_eq] using this
  have h2 := OrderHomotopy.le_pathMax (c.coord p) τ
  simp only [coord, ContinuousMap.comp_apply] at h2
  unfold slack at hc
  have hp0 := c.nonneg (p τ)
  constructor
  · unfold top' coord
    linarith [(abs_lt.mp hc).2, (abs_le.mp hd).2]
  · rw [abs_lt]
    constructor
    · have := le_max_right 0 (c.Φ (q τ) + corr (c.Φ x.1 - c.Φ (q 0)) (c.Φ x.2 - c.Φ (q 1)) τ)
      linarith [(abs_lt.mp hc).1, (abs_le.mp hd).1]
    · rcases le_total 0 (c.Φ (q τ) + corr (c.Φ x.1 - c.Φ (q 0)) (c.Φ x.2 - c.Φ (q 1)) τ)
        with h' | h'
      · rw [max_eq_right h']
        linarith [(abs_lt.mp hc).2, (abs_le.mp hd).2]
      · rw [max_eq_left h']
        linarith [h.pos]

theorem clampTo_val_of_le (h : c.Admissible p ε) {y : ℝ} (hy : y ≤ top' h) :
    ((clampTo h y : Ico (0 : ℝ) c.β) : ℝ) = max 0 y := by
  simp [clampTo, projIcc, min_eq_right hy]

/-- `ψ` inverts `Φ` on `J`, in a form convenient for rewriting. -/
theorem ψ_of_val_eq {x : T} {s : Ico (0 : ℝ) c.β} (hs : (s : ℝ) = c.Φ x) : c.ψ s = x := by
  have hx : c.Φ x < c.β := hs ▸ s.2.2
  have : s = ⟨c.Φ x, c.nonneg x, hx⟩ := Subtype.ext hs
  rw [this, c.ψ_Φ x hx]

theorem Φ_sect (h : c.Admissible p ε) {q : C(I, T)} {x : T × T}
    (hx : x ∈ c.Wq (p := p) (ε := ε) q) (τ : I) :
    c.Φ (c.sect h q x τ) =
      max 0 (c.Φ (q τ) + corr (c.Φ x.1 - c.Φ (q 0)) (c.Φ x.2 - c.Φ (q 1)) τ) := by
  rw [sect_apply, c.Φ_ψ, clampTo_val_of_le h (perturbed_bounds h hx τ).1]

theorem sect_mem_V (h : c.Admissible p ε) {q : C(I, T)} {x : T × T}
    (hx : x ∈ c.Wq (p := p) (ε := ε) q) : c.sect h q x ∈ c.V p ε := by
  rw [mem_V_iff h.pos]
  intro τ
  rw [Φ_sect h hx]
  exact (perturbed_bounds h hx τ).2

theorem corr_zero (d₀ d₁ : ℝ) : corr d₀ d₁ 0 = d₀ := by simp [corr]

theorem corr_one (d₀ d₁ : ℝ) : corr d₀ d₁ 1 = d₁ := by simp [corr]

theorem sect_zero (h : c.Admissible p ε) {q : C(I, T)} {x : T × T}
    (hx : x ∈ c.Wq (p := p) (ε := ε) q) : c.sect h q x 0 = x.1 := by
  apply ψ_of_val_eq
  rw [clampTo_val_of_le h (perturbed_bounds h hx 0).1, corr_zero]
  simp only [add_sub_cancel]
  exact max_eq_right (c.nonneg x.1)

theorem sect_one (h : c.Admissible p ε) {q : C(I, T)} {x : T × T}
    (hx : x ∈ c.Wq (p := p) (ε := ε) q) : c.sect h q x 1 = x.2 := by
  apply ψ_of_val_eq
  rw [clampTo_val_of_le h (perturbed_bounds h hx 1).1, corr_one]
  simp only [add_sub_cancel]
  exact max_eq_right (c.nonneg x.2)

theorem endpointMap_sect (h : c.Admissible p ε) {q : C(I, T)} {x : T × T}
    (hx : x ∈ c.Wq (p := p) (ε := ε) q) : endpointMap T (c.sect h q x) = x := by
  rw [endpointMap_apply, sect_zero h hx, sect_one h hx]

theorem sect_self (h : c.Admissible p ε) {q : C(I, T)} (hq : q ∈ c.V p ε) :
    c.sect h q (endpointMap T q) = q := by
  ext τ
  apply ψ_of_val_eq
  have hx := mem_Wq_self (c := c) hq
  rw [clampTo_val_of_le h (perturbed_bounds h hx τ).1]
  simp only [endpointMap_apply, sub_self, corr, mul_zero, add_zero]
  exact max_eq_right (c.nonneg _)

/-- **Actual image.** The endpoint map sends the chart ball `V` onto `W`. -/
theorem endpointMap_image_V (h : c.Admissible p ε) :
    endpointMap T '' c.V p ε = c.W p ε := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_V_iff h.pos] at hq
    exact ⟨hq 0, hq 1⟩
  · intro hx
    have hp : p ∈ c.V p ε := by
      change dist (c.coord p) (c.coord p) < ε
      rw [dist_self]; exact h.pos
    have hxp : x ∈ c.Wq (p := p) (ε := ε) p := by
      simp only [Wq, slack, dist_self, sub_zero]
      exact hx
    exact ⟨c.sect h p x, sect_mem_V h hxp, endpointMap_sect h hxp⟩

/-- **Openness.** The endpoint map is open on the chart ball `V`. -/
theorem isOpen_image_of_subset_V (h : c.Admissible p ε) {N : Set C(I, T)} (hN : IsOpen N)
    (hNV : N ⊆ c.V p ε) : IsOpen (endpointMap T '' N) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨q, hqN, rfl⟩
  have hqV := hNV hqN
  have hO : IsOpen (c.Wq (p := p) (ε := ε) q ∩ (c.sect h q) ⁻¹' N) :=
    (isOpen_Wq q).inter (hN.preimage (c.sect h q).continuous)
  have hmem : endpointMap T q ∈ c.Wq (p := p) (ε := ε) q ∩ (c.sect h q) ⁻¹' N :=
    ⟨mem_Wq_self hqV, by rw [Set.mem_preimage, sect_self h hqV]; exact hqN⟩
  refine Filter.mem_of_superset (hO.mem_nhds hmem) ?_
  rintro x ⟨hxW, hxN⟩
  exact ⟨c.sect h q x, hxN, endpointMap_sect h hxW⟩

/-! ### Convexity: path-connectedness of the ball and of its fibres -/

/-- Linear interpolation of the chart coordinates of two paths. -/
def interp (h : c.Admissible p ε) (q₀ q₁ : C(I, T)) : C(I, C(I, T)) :=
  ContinuousMap.curry
    ⟨fun x : I × I => c.ψ (clampTo h ((1 - (x.1 : ℝ)) * c.Φ (q₀ x.2) + (x.1 : ℝ) * c.Φ (q₁ x.2))),
      by fun_prop⟩

theorem interp_coord_bounds (h : c.Admissible p ε) {q₀ q₁ : C(I, T)} (h₀ : q₀ ∈ c.V p ε)
    (h₁ : q₁ ∈ c.V p ε) (s τ : I) :
    0 ≤ (1 - (s : ℝ)) * c.Φ (q₀ τ) + (s : ℝ) * c.Φ (q₁ τ) ∧
    (1 - (s : ℝ)) * c.Φ (q₀ τ) + (s : ℝ) * c.Φ (q₁ τ) ≤ top' h ∧
    |(1 - (s : ℝ)) * c.Φ (q₀ τ) + (s : ℝ) * c.Φ (q₁ τ) - c.Φ (p τ)| < ε := by
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have a₀ := (mem_V_iff h.pos).mp h₀ τ
  have a₁ := (mem_V_iff h.pos).mp h₁ τ
  have b₀ := coord_le_top' h h₀ τ
  have b₁ := coord_le_top' h h₁ τ
  have n₀ := c.nonneg (q₀ τ)
  have n₁ := c.nonneg (q₁ τ)
  refine ⟨by positivity, ?_, ?_⟩
  · nlinarith
  · have : (1 - (s : ℝ)) * c.Φ (q₀ τ) + (s : ℝ) * c.Φ (q₁ τ) - c.Φ (p τ) =
        (1 - (s : ℝ)) * (c.Φ (q₀ τ) - c.Φ (p τ)) + (s : ℝ) * (c.Φ (q₁ τ) - c.Φ (p τ)) := by
      ring
    rw [this]
    calc |(1 - (s : ℝ)) * (c.Φ (q₀ τ) - c.Φ (p τ)) + (s : ℝ) * (c.Φ (q₁ τ) - c.Φ (p τ))|
        ≤ (1 - (s : ℝ)) * |c.Φ (q₀ τ) - c.Φ (p τ)| + (s : ℝ) * |c.Φ (q₁ τ) - c.Φ (p τ)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hs0]
      _ < ε := by
          rcases eq_or_lt_of_le hs0 with hs | hs
          · rw [← hs]; simpa using a₀
          · nlinarith

theorem Φ_interp (h : c.Admissible p ε) {q₀ q₁ : C(I, T)} (h₀ : q₀ ∈ c.V p ε)
    (h₁ : q₁ ∈ c.V p ε) (s τ : I) :
    c.Φ (c.interp h q₀ q₁ s τ) = (1 - (s : ℝ)) * c.Φ (q₀ τ) + (s : ℝ) * c.Φ (q₁ τ) := by
  obtain ⟨b0, b1, -⟩ := interp_coord_bounds h h₀ h₁ s τ
  change c.Φ (c.ψ (clampTo h _)) = _
  rw [c.Φ_ψ, clampTo_val_of_le h b1, max_eq_right b0]

theorem interp_mem_V (h : c.Admissible p ε) {q₀ q₁ : C(I, T)} (h₀ : q₀ ∈ c.V p ε)
    (h₁ : q₁ ∈ c.V p ε) (s : I) : c.interp h q₀ q₁ s ∈ c.V p ε := by
  rw [mem_V_iff h.pos]
  intro τ
  rw [Φ_interp h h₀ h₁]
  exact (interp_coord_bounds h h₀ h₁ s τ).2.2

theorem interp_zero (h : c.Admissible p ε) {q₀ q₁ : C(I, T)} (h₀ : q₀ ∈ c.V p ε)
    (h₁ : q₁ ∈ c.V p ε) : c.interp h q₀ q₁ 0 = q₀ := by
  ext τ
  apply ψ_of_val_eq
  obtain ⟨b0, b1, -⟩ := interp_coord_bounds h h₀ h₁ 0 τ
  rw [clampTo_val_of_le h b1, max_eq_right b0]
  simp

theorem interp_one (h : c.Admissible p ε) {q₀ q₁ : C(I, T)} (h₀ : q₀ ∈ c.V p ε)
    (h₁ : q₁ ∈ c.V p ε) : c.interp h q₀ q₁ 1 = q₁ := by
  ext τ
  apply ψ_of_val_eq
  obtain ⟨b0, b1, -⟩ := interp_coord_bounds h h₀ h₁ 1 τ
  rw [clampTo_val_of_le h b1, max_eq_right b0]
  simp

/-- The interpolation keeps any parameter at which the two paths agree. -/
theorem interp_of_eq (h : c.Admissible p ε) {q₀ q₁ : C(I, T)} (h₀ : q₀ ∈ c.V p ε)
    (h₁ : q₁ ∈ c.V p ε) (s τ : I) (hτ : q₀ τ = q₁ τ) : c.interp h q₀ q₁ s τ = q₀ τ := by
  apply ψ_of_val_eq
  obtain ⟨b0, b1, -⟩ := interp_coord_bounds h h₀ h₁ s τ
  rw [clampTo_val_of_le h b1, max_eq_right b0, ← hτ]
  ring

/-- The chart ball is path connected. -/
theorem isPathConnected_V (h : c.Admissible p ε) : IsPathConnected (c.V p ε) := by
  have hp : p ∈ c.V p ε := by
    change dist (c.coord p) (c.coord p) < ε
    rw [dist_self]; exact h.pos
  refine ⟨p, hp, fun {q} hq => ?_⟩
  refine ⟨⟨c.interp h p q, interp_zero h hp hq, interp_one h hp hq⟩, fun s => ?_⟩
  exact interp_mem_V h hp hq s

/-- The fibres of `V → W` are path connected. -/
theorem joinedIn_fibre (h : c.Admissible p ε) {q₀ q₁ : C(I, T)} (h₀ : q₀ ∈ c.V p ε)
    (h₁ : q₁ ∈ c.V p ε) (he : endpointMap T q₀ = endpointMap T q₁) :
    JoinedIn (c.V p ε ∩ endpointMap T ⁻¹' {endpointMap T q₀}) q₀ q₁ := by
  simp only [endpointMap_apply, Prod.mk.injEq] at he
  refine ⟨⟨c.interp h q₀ q₁, interp_zero h h₀ h₁, interp_one h h₀ h₁⟩, fun s => ?_⟩
  refine ⟨interp_mem_V h h₀ h₁ s, ?_⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, endpointMap_apply, Prod.mk.injEq]
  exact ⟨interp_of_eq h h₀ h₁ s 0 he.1, interp_of_eq h h₀ h₁ s 1 he.2⟩

/-! ### The relative homotopy preserves uniform balls of monotone charts -/

section Homotopy

variable {T : Type u} [TopologicalSpace T] [LinearOrder T] [OrderTopology T]

/-- **Preservation of designated bounded domains.** For a chart whose
coordinate is monotone, the relative homotopy of two paths in a uniform chart
ball `V` stays in `V` (its interval constraints included). -/
theorem relHomotopy_mem_V {c : BottomChart T} (hΦ : Monotone c.Φ) {p : C(I, T)} {ε : ℝ}
    (hε : 0 < ε) (q : OrderHomotopy.SameStart (T := T)) (h₀ : q.1.1 ∈ c.V p ε)
    (h₁ : q.1.2 ∈ c.V p ε) (u : I) : OrderHomotopy.relHomotopy (q, u) ∈ c.V p ε := by
  rw [mem_V_iff hε]
  intro τ
  obtain ⟨hl, hu⟩ := OrderHomotopy.relHomotopy_bounds q u τ
  have a₀ := abs_lt.mp ((mem_V_iff hε).mp h₀ τ)
  have a₁ := abs_lt.mp ((mem_V_iff hε).mp h₁ τ)
  have l : min (c.Φ (q.1.1 τ)) (c.Φ (q.1.2 τ)) ≤ c.Φ (OrderHomotopy.relHomotopy (q, u) τ) := by
    rw [← hΦ.map_min]; exact hΦ hl
  have r : c.Φ (OrderHomotopy.relHomotopy (q, u) τ) ≤ max (c.Φ (q.1.1 τ)) (c.Φ (q.1.2 τ)) := by
    rw [← hΦ.map_max]; exact hΦ hu
  rw [abs_lt]
  constructor
  · rcases min_choice (c.Φ (q.1.1 τ)) (c.Φ (q.1.2 τ)) with h | h <;> rw [h] at l <;> linarith
  · rcases max_choice (c.Φ (q.1.1 τ)) (c.Φ (q.1.2 τ)) with h | h <;> rw [h] at r <;> linarith

/-- The relative homotopy is a homotopy over the endpoint map. -/
theorem endpointMap_relHomotopy (q : OrderHomotopy.SameStart (T := T))
    (h1 : q.1.1 1 = q.1.2 1) (u : I) :
    endpointMap T (OrderHomotopy.relHomotopy (q, u)) = endpointMap T q.1.1 := by
  simp only [endpointMap_apply]
  rw [OrderHomotopy.relHomotopy_of_eq q u 0 q.2, OrderHomotopy.relHomotopy_of_eq q u 1 h1]

end Homotopy

end BottomChart

end RealContinuity
