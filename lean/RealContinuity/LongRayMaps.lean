import RealContinuity.LongRayChart

/-!
# The designated maps `q` and `r` on the closed long ray

* `qMap : L → Prop` (the Sierpiński space, `o = True` for finite points,
  `c = False` for `∞`) is a continuous open surjection.
* Two finite points are joined by a path whose values stay between them.
* Compact-open neighbourhoods of the constant path at `∞` contain all paths
  in some tail `(a, ∞]`.
* The endpoint map `r : C(I, L) → L × L` takes values in
  `K = {(x, y) | x = ∞ ↔ y = ∞}`, maps onto `K`, and is open as a map to `K`:
  at bounded paths by the chart lemma, at the constant path at `∞` by tails.
-/

noncomputable section

open Set Topology Filter unitInterval

namespace RealContinuity

/-! ### Sierpiński space and `q` -/

/-- `q(x) = (x ≠ ∞)`. -/
def qMap : C(L, Prop) :=
  ⟨fun x => x ≠ ⊤, continuous_Prop.mpr (by
    have : {x : L | x ≠ ⊤} = Iio ⊤ := by ext x; simp [lt_top_iff_ne_top]
    rw [this]; exact isOpen_Iio)⟩

theorem qMap_apply (x : L) : qMap x = (x ≠ ⊤) := rfl

theorem qMap_surjective : Function.Surjective qMap := by
  intro P
  by_cases hP : P
  · refine ⟨ordPt (Classical.arbitrary W), ?_⟩
    simp only [qMap_apply, eq_iff_iff, iff_true_intro hP, iff_true]
    exact (ordPt_lt_top _).ne
  · exact ⟨⊤, by simp [qMap_apply, hP]⟩

/-- Every neighbourhood of `∞` contains finite points. -/
theorem exists_coe_mem_of_isOpen {U : Set L} (hU : IsOpen U) (htop : (⊤ : L) ∈ U) :
    ∃ x : L₀, (x : L) ∈ U := by
  have : (𝓝 (⊤ : L)).HasBasis (fun a : L => a < ⊤) Ioi := nhds_top_basis
  obtain ⟨a, ha, haU⟩ := this.mem_iff.mp (hU.mem_nhds htop)
  obtain ⟨a₀, rfl⟩ := WithTop.ne_top_iff_exists.mp ha.ne
  obtain ⟨c, hc⟩ := exists_ordPt_gt a₀
  exact ⟨_, haU (show (a₀ : L) < ordPt c from hc)⟩

theorem qMap_isOpenMap : IsOpenMap qMap := by
  intro U hU
  by_cases htop : (⊤ : L) ∈ U
  · obtain ⟨x, hx⟩ := exists_coe_mem_of_isOpen hU htop
    have : qMap '' U = univ := by
      ext P
      simp only [mem_image, mem_univ, iff_true]
      by_cases hP : P
      · exact ⟨x, hx, by simp [qMap_apply, hP, WithTop.coe_ne_top]⟩
      · exact ⟨⊤, htop, by simp [qMap_apply, hP]⟩
    rw [this]; exact isOpen_univ
  · have hsub : qMap '' U ⊆ {True} := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [mem_singleton_iff, qMap_apply, eq_iff_iff, iff_true]
      exact fun h => htop (h ▸ hx)
    rcases (Set.subset_singleton_iff_eq.mp hsub) with h | h
    · rw [h]; exact isOpen_empty
    · rw [h]; exact TopologicalSpace.isOpen_generateFrom_of_mem rfl

/-! ### Paths between finite points stay between them -/

theorem Chart.ψ_mono (b : W) : Monotone (Chart.chart b).ψ := by
  intro s s' h
  change (((Chart.segIso b).symm s : Iio (ordPt b)) : L) ≤ (((Chart.segIso b).symm s' : _) : L)
  exact (Chart.segIso b).symm.monotone h

theorem exists_path_between (x y : L₀) :
    ∃ γ : C(I, L), γ 0 = x ∧ γ 1 = y ∧ ∀ t, min (x : L) y ≤ γ t ∧ γ t ≤ max (x : L) y := by
  obtain ⟨b₁, hb₁⟩ := exists_ordPt_gt x
  obtain ⟨b₂, hb₂⟩ := exists_ordPt_gt y
  set b := max b₁ b₂
  have hx : (x : L) < ordPt b := hb₁.trans_le (ordPt_le_ordPt (le_max_left b₁ b₂))
  have hy : (y : L) < ordPt b := hb₂.trans_le (ordPt_le_ordPt (le_max_right b₁ b₂))
  set c := Chart.chart b
  have hxJ : c.Φ x < c.β := Chart.Φfun_lt_S_of_lt_ordPt b hx
  have hyJ : c.Φ y < c.β := Chart.Φfun_lt_S_of_lt_ordPt b hy
  have hmem : ∀ t : I, (1 - (t : ℝ)) * c.Φ x + (t : ℝ) * c.Φ y ∈ Ico (0 : ℝ) c.β := by
    intro t
    have hx0 := c.nonneg (x : L); have hy0 := c.nonneg (y : L)
    have h0 := t.2.1; have h1 := t.2.2
    constructor
    · have : 0 ≤ 1 - (t : ℝ) := by linarith
      positivity
    · have e : c.β - ((1 - (t : ℝ)) * c.Φ x + (t : ℝ) * c.Φ y) =
          (1 - (t : ℝ)) * (c.β - c.Φ x) + (t : ℝ) * (c.β - c.Φ y) := by ring
      have m0 : 0 < min (c.β - c.Φ x) (c.β - c.Φ y) := lt_min (by linarith) (by linarith)
      have k1 : (1 - (t : ℝ)) * min (c.β - c.Φ x) (c.β - c.Φ y) ≤ (1 - (t : ℝ)) * (c.β - c.Φ x) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
      have k2 : (t : ℝ) * min (c.β - c.Φ x) (c.β - c.Φ y) ≤ (t : ℝ) * (c.β - c.Φ y) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) h0
      have : 0 < c.β - ((1 - (t : ℝ)) * c.Φ x + (t : ℝ) * c.Φ y) := by
        rw [e]; nlinarith
      linarith
  let s : I → Ico (0 : ℝ) c.β := fun t => ⟨(1 - (t : ℝ)) * c.Φ x + (t : ℝ) * c.Φ y, hmem t⟩
  have hs : Continuous s := by
    have : Continuous fun t : I => (1 - (t : ℝ)) * c.Φ x + (t : ℝ) * c.Φ y := by fun_prop
    exact this.subtype_mk _
  refine ⟨⟨fun t => c.ψ (s t), c.ψ.continuous.comp hs⟩, ?_, ?_, fun t => ?_⟩
  · change c.ψ (s 0) = x
    have : s 0 = ⟨c.Φ x, c.nonneg _, hxJ⟩ := Subtype.ext (by simp [s])
    rw [this, c.ψ_Φ _ hxJ]
  · change c.ψ (s 1) = y
    have : s 1 = ⟨c.Φ y, c.nonneg _, hyJ⟩ := Subtype.ext (by simp [s])
    rw [this, c.ψ_Φ _ hyJ]
  · have hxψ : c.ψ ⟨c.Φ x, c.nonneg _, hxJ⟩ = x := c.ψ_Φ _ hxJ
    have hyψ : c.ψ ⟨c.Φ y, c.nonneg _, hyJ⟩ = y := c.ψ_Φ _ hyJ
    have h0 := t.2.1; have h1 := t.2.2
    rcases le_total (c.Φ x) (c.Φ y) with hxy | hxy
    · have l : (⟨c.Φ x, c.nonneg _, hxJ⟩ : Ico (0 : ℝ) c.β) ≤ s t := by
        change c.Φ x ≤ (1 - (t : ℝ)) * c.Φ x + (t : ℝ) * c.Φ y; nlinarith
      have r : s t ≤ (⟨c.Φ y, c.nonneg _, hyJ⟩ : Ico (0 : ℝ) c.β) := by
        change (1 - (t : ℝ)) * c.Φ x + (t : ℝ) * c.Φ y ≤ c.Φ y; nlinarith
      have l' := Chart.ψ_mono b l
      have r' := Chart.ψ_mono b r
      rw [hxψ] at l'; rw [hyψ] at r'
      exact ⟨(min_le_left _ _).trans l', r'.trans (le_max_right _ _)⟩
    · have l : (⟨c.Φ y, c.nonneg _, hyJ⟩ : Ico (0 : ℝ) c.β) ≤ s t := by
        change c.Φ y ≤ (1 - (t : ℝ)) * c.Φ x + (t : ℝ) * c.Φ y; nlinarith
      have r : s t ≤ (⟨c.Φ x, c.nonneg _, hxJ⟩ : Ico (0 : ℝ) c.β) := by
        change (1 - (t : ℝ)) * c.Φ x + (t : ℝ) * c.Φ y ≤ c.Φ x; nlinarith
      have l' := Chart.ψ_mono b l
      have r' := Chart.ψ_mono b r
      rw [hyψ] at l'; rw [hxψ] at r'
      exact ⟨(min_le_right _ _).trans l', r'.trans (le_max_left _ _)⟩

/-! ### Tails at the constant path at `∞` -/

/-- The constant path at `∞`. -/
def constTop : C(I, L) := ContinuousMap.const _ ⊤

/-- Every compact-open neighbourhood of the constant path at `∞` contains all
paths into some tail `(a, ∞]`. -/
theorem exists_tail_subset {N : Set C(I, L)} (hN : N ∈ 𝓝 constTop) :
    ∃ a : L, a < ⊤ ∧ {g : C(I, L) | ∀ t, a < g t} ⊆ N := by
  -- the filter of tails
  let F : Filter C(I, L) := ⨅ a : Iio (⊤ : L), 𝓟 {g : C(I, L) | ∀ t, (a : L) < g t}
  have hdir : Directed (· ≥ ·) fun a : Iio (⊤ : L) => 𝓟 {g : C(I, L) | ∀ t, (a : L) < g t} := by
    intro a a'
    refine ⟨⟨max (a : L) a', Set.mem_Iio.mpr (max_lt a.2 a'.2)⟩, ?_, ?_⟩
    · exact principal_mono.mpr fun g hg t => (le_max_left _ _).trans_lt (hg t)
    · exact principal_mono.mpr fun g hg t => (le_max_right _ _).trans_lt (hg t)
  have hF : F ≤ 𝓝 constTop := by
    rw [ContinuousMap.nhds_compactOpen]
    refine le_iInf₂ fun K _ => le_iInf₂ fun U hU => le_iInf fun hKU => ?_
    by_cases hK : K.Nonempty
    · obtain ⟨k, hk⟩ := hK
      have htop : (⊤ : L) ∈ U := hKU hk
      have hbas : (𝓝 (⊤ : L)).HasBasis (fun a : L => a < ⊤) Ioi := nhds_top_basis
      obtain ⟨a, ha, haU⟩ := hbas.mem_iff.mp (hU.mem_nhds htop)
      refine iInf_le_of_le ⟨a, ha⟩ (principal_mono.mpr fun g hg x _ => haU (hg x))
    · rw [not_nonempty_iff_eq_empty] at hK
      subst hK
      exact le_principal_iff.mpr (Filter.univ_mem' fun g => by simp [MapsTo])
  have hmem : N ∈ F := hF hN
  have : Nonempty (Iio (⊤ : L)) := ⟨⟨ordPt (Classical.arbitrary W), ordPt_lt_top _⟩⟩
  rw [mem_iInf_of_directed hdir] at hmem
  obtain ⟨⟨a, ha⟩, haN⟩ := hmem
  exact ⟨a, ha, haN⟩

/-! ### The endpoint map onto `K` -/

/-- The kernel pair of `q`: both points finite, or both `∞`. -/
def Kset : Set (L × L) := {p | p.1 = ⊤ ↔ p.2 = ⊤}

theorem endpointMap_mem_Kset (γ : C(I, L)) : endpointMap L γ ∈ Kset := by
  rcases path_const_top_or_bounded γ with h | ⟨b, hb⟩
  · simp [Kset, h]
  · simp [Kset, (lt_top_of_lt (hb 0)).ne, (lt_top_of_lt (hb 1)).ne]
where
  lt_top_of_lt {x : L} {b : W} (h : x < ordPt b) : x < ⊤ := h.trans (ordPt_lt_top b)

theorem image_endpointMap : range (endpointMap L) = Kset := by
  ext p
  constructor
  · rintro ⟨γ, rfl⟩; exact endpointMap_mem_Kset γ
  · intro hp
    obtain ⟨x, y⟩ := p
    by_cases hx : x = ⊤
    · have hy : y = ⊤ := hp.mp hx
      subst hx; subst hy
      exact ⟨constTop, rfl⟩
    · have hy : y ≠ ⊤ := fun h => hx (hp.mpr h)
      obtain ⟨x₀, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
      obtain ⟨y₀, rfl⟩ := WithTop.ne_top_iff_exists.mp hy
      obtain ⟨γ, h0, h1, -⟩ := exists_path_between x₀ y₀
      exact ⟨γ, by simp [endpointMap_apply, h0, h1]⟩

/-- **Openness of `r` onto `K`.** The endpoint image of an open set of paths is
a neighbourhood, within `K`, of each of its points. -/
theorem endpointMap_open {N : Set C(I, L)} (hN : IsOpen N) {γ : C(I, L)} (hγ : γ ∈ N) :
    ∃ O : Set (L × L), IsOpen O ∧ endpointMap L γ ∈ O ∧ O ∩ Kset ⊆ endpointMap L '' N := by
  rcases path_const_top_or_bounded γ with h | ⟨b, hb⟩
  · -- the constant path at `∞`
    have hγ' : γ = constTop := ContinuousMap.ext h
    subst hγ'
    obtain ⟨a, ha, haN⟩ := exists_tail_subset (hN.mem_nhds hγ)
    refine ⟨Ioi a ×ˢ Ioi a, isOpen_Ioi.prod isOpen_Ioi, ⟨ha, ha⟩, ?_⟩
    rintro ⟨x, y⟩ ⟨⟨hxa, hya⟩, hK⟩
    by_cases hx : x = ⊤
    · have hy : y = ⊤ := hK.mp hx
      subst hx; subst hy
      exact ⟨constTop, mem_of_mem_nhds (hN.mem_nhds hγ), rfl⟩
    · have hy : y ≠ ⊤ := fun h => hx (hK.mpr h)
      obtain ⟨x₀, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
      obtain ⟨y₀, rfl⟩ := WithTop.ne_top_iff_exists.mp hy
      obtain ⟨p, h0, h1, hp⟩ := exists_path_between x₀ y₀
      refine ⟨p, haN fun t => ?_, by simp [endpointMap_apply, h0, h1]⟩
      exact (lt_min hxa hya).trans_le (hp t).1
  · -- a bounded path: the chart lemma
    obtain ⟨ε, hε⟩ := exists_admissible hb
    set c := Chart.chart b
    have hγV : γ ∈ c.V γ ε := by
      change dist (c.coord γ) (c.coord γ) < ε
      rw [dist_self]; exact hε.pos
    refine ⟨endpointMap L '' (N ∩ c.V γ ε),
      c.isOpen_image_of_subset_V hε (hN.inter (c.isOpen_V γ ε)) inter_subset_right,
      ⟨γ, ⟨hγ, hγV⟩, rfl⟩, ?_⟩
    rintro _ ⟨⟨p, hp, rfl⟩, -⟩
    exact ⟨p, hp.1, rfl⟩

end RealContinuity
