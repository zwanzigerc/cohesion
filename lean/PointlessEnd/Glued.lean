import PointlessEnd.Cohen
import PointlessEnd.RealCuts

/-!
# The pointless-end locale `L_e`

For `e : P`, the frame of the pointless-end locale `L_e` is the Artin gluing of the open
interval `(0, 1)` and the endpoint locale with frame `↓e`:

  `O(L_e) = {(V, d) | V ⊆ (0, 1) open, d ≤ e, d ≠ ⊥ → ∃ ε > 0, (0, ε) ⊆ V}`,

ordered componentwise. Joins and finite meets are componentwise; infinite meets are joins
of lower bounds. The endpoint `↓e` is glued at `0`: a neighbourhood of a nonzero part of
the end contains an initial interval of the collar.

* `tHom e : O(ℝ) → O(L_e)` is the coordinate `t : L_e → ℝ`, extending the inclusion of
  the collar and sending the end to `0`: `t^*(W) = (W ∩ (0,1), e if 0 ∈ W else ⊥)`.
* `u e = (⊤, ⊥)` is the collar, `t^*(0, ∞) = u e`, and `u e ≠ ⊤` when `e ≠ ⊥`.
* Every open is `t^*(V) ⊔ (t^*(-∞, ε) ⊓ D d)` with `D d = ((0,1), d)` (`eq_decomp`), so a
  frame homomorphism out of `O(L_e)` is determined by its restrictions along `t^*` and `D`
  (`glue_ext`), and conversely compatible data `(σ, δ)` define one (`GlueData.toHom`).
* **Points.** Every point of `L_e` is a collar point (`point_eq_collarPt`): the end has
  no points since `P` has none. Every nonzero open contains a point, and `O(L_e)` is
  connected.
-/

noncomputable section

open Set TopologicalSpace

namespace PointlessEnd

/-- **Opens of the pointless-end locale `L_e`.** -/
@[ext] structure G (e : P) where
  /-- The collar component, an open subset of `(0, 1)`. -/
  V : Opens ℝ
  /-- The endpoint component, below `e`. -/
  d : P
  hV : (V : Set ℝ) ⊆ Ioo 0 1
  hd : d ≤ e
  glue : d ≠ ⊥ → ∃ ε : ℝ, 0 < ε ∧ Ioo 0 ε ⊆ (V : Set ℝ)

namespace G

variable {e : P}

theorem d_eq_bot_of_V {x : G e} (h : (x.V : Set ℝ) = ∅) : x.d = ⊥ := by
  by_contra hne
  obtain ⟨ε, hε, hsub⟩ := x.glue hne
  have : ε / 2 ∈ (x.V : Set ℝ) := hsub ⟨by linarith, by linarith⟩
  rw [h] at this
  exact this

instance : PartialOrder (G e) where
  le x y := x.V ≤ y.V ∧ x.d ≤ y.d
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := G.ext (le_antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2)

theorem le_def {x y : G e} : x ≤ y ↔ x.V ≤ y.V ∧ x.d ≤ y.d := Iff.rfl

/-- Binary joins, componentwise. -/
def sup' (x y : G e) : G e where
  V := x.V ⊔ y.V
  d := x.d ⊔ y.d
  hV := union_subset x.hV y.hV
  hd := sup_le x.hd y.hd
  glue h := by
    by_cases hx : x.d = ⊥
    · have hy : y.d ≠ ⊥ := fun hy => h (by rw [hx, hy, sup_bot_eq])
      obtain ⟨ε, hε, hsub⟩ := y.glue hy
      exact ⟨ε, hε, hsub.trans (SetLike.coe_subset_coe.mpr le_sup_right)⟩
    · obtain ⟨ε, hε, hsub⟩ := x.glue hx
      exact ⟨ε, hε, hsub.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩

/-- Binary meets, componentwise. -/
def inf' (x y : G e) : G e where
  V := x.V ⊓ y.V
  d := x.d ⊓ y.d
  hV := fun _ ht => x.hV ht.1
  hd := inf_le_left.trans x.hd
  glue h := by
    have hx : x.d ≠ ⊥ := fun hx => h (by rw [hx, bot_inf_eq])
    have hy : y.d ≠ ⊥ := fun hy => h (by rw [hy, inf_bot_eq])
    obtain ⟨ε₁, h₁, s₁⟩ := x.glue hx
    obtain ⟨ε₂, h₂, s₂⟩ := y.glue hy
    exact ⟨min ε₁ ε₂, lt_min h₁ h₂, fun t ht =>
      ⟨s₁ ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩, s₂ ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩⟩⟩

/-- Arbitrary joins, componentwise. -/
def sSup' (S : Set (G e)) : G e where
  V := ⨆ x ∈ S, x.V
  d := ⨆ x ∈ S, x.d
  hV := by
    intro t ht
    have ht' : t ∈ (⨆ x ∈ S, x.V : Opens ℝ) := ht
    obtain ⟨x, hx'⟩ := Opens.mem_iSup.mp ht'
    obtain ⟨-, hx⟩ := Opens.mem_iSup.mp hx'
    exact x.hV hx
  hd := iSup₂_le fun x _ => x.hd
  glue h := by
    by_contra hall
    apply h
    refine le_antisymm (iSup₂_le fun x hx => ?_) bot_le
    by_contra hne
    obtain ⟨ε, hε, hsub⟩ := x.glue (fun h' => hne (h'.le))
    exact hall ⟨ε, hε, hsub.trans (SetLike.coe_subset_coe.mpr
      (le_iSup₂ (f := fun x (_ : x ∈ S) => x.V) x hx))⟩

theorem isLUB_sSup' (S : Set (G e)) : IsLUB S (sSup' S) :=
  ⟨fun x hx => ⟨le_iSup₂ (f := fun x (_ : x ∈ S) => x.V) x hx,
      le_iSup₂ (f := fun x (_ : x ∈ S) => x.d) x hx⟩,
    fun _ hb => ⟨iSup₂_le fun _ hx => (hb hx).1, iSup₂_le fun _ hx => (hb hx).2⟩⟩

/-- The top open `((0, 1), e)`. -/
def top' : G e where
  V := ⟨Ioo 0 1, isOpen_Ioo⟩
  d := e
  hV := subset_rfl
  hd := le_rfl
  glue _ := ⟨1, one_pos, subset_rfl⟩

/-- The bottom open `(∅, ⊥)`. -/
def bot' : G e where
  V := ⊥
  d := ⊥
  hV := by simp
  hd := bot_le
  glue h := absurd rfl h

instance : CompleteLattice (G e) where
  sup := sup'
  le_sup_left _ _ := ⟨le_sup_left, le_sup_left⟩
  le_sup_right _ _ := ⟨le_sup_right, le_sup_right⟩
  sup_le _ _ _ h₁ h₂ := ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩
  inf := inf'
  inf_le_left _ _ := ⟨inf_le_left, inf_le_left⟩
  inf_le_right _ _ := ⟨inf_le_right, inf_le_right⟩
  le_inf _ _ _ h₁ h₂ := ⟨le_inf h₁.1 h₂.1, le_inf h₁.2 h₂.2⟩
  sSup := sSup'
  isLUB_sSup := isLUB_sSup'
  sInf S := sSup' {y | ∀ x ∈ S, y ≤ x}
  isGLB_sInf _ := ⟨fun x hx => (isLUB_sSup' _).2 fun _ hy => hy x hx,
    fun _ hb => (isLUB_sSup' _).1 hb⟩
  top := top'
  bot := bot'
  le_top x := ⟨fun _ ht => x.hV ht, x.hd⟩
  bot_le _ := ⟨bot_le, bot_le⟩

@[simp] theorem V_sup (x y : G e) : (x ⊔ y).V = x.V ⊔ y.V := rfl
@[simp] theorem d_sup (x y : G e) : (x ⊔ y).d = x.d ⊔ y.d := rfl
@[simp] theorem V_inf (x y : G e) : (x ⊓ y).V = x.V ⊓ y.V := rfl
@[simp] theorem d_inf (x y : G e) : (x ⊓ y).d = x.d ⊓ y.d := rfl
@[simp] theorem V_sSup (S : Set (G e)) : (sSup S).V = ⨆ x ∈ S, x.V := rfl
@[simp] theorem d_sSup (S : Set (G e)) : (sSup S).d = ⨆ x ∈ S, x.d := rfl
@[simp] theorem coe_V_top : ((⊤ : G e).V : Set ℝ) = Ioo 0 1 := rfl
@[simp] theorem d_top : (⊤ : G e).d = e := rfl
@[simp] theorem V_bot : (⊥ : G e).V = ⊥ := rfl
@[simp] theorem d_bot : (⊥ : G e).d = ⊥ := rfl

theorem V_iSup {ι : Sort*} (f : ι → G e) : (⨆ i, f i).V = ⨆ i, (f i).V := by
  change (sSup (range f)).V = _
  rw [V_sSup, iSup_range]

theorem d_iSup {ι : Sort*} (f : ι → G e) : (⨆ i, f i).d = ⨆ i, (f i).d := by
  change (sSup (range f)).d = _
  rw [d_sSup, iSup_range]

/-- **`O(L_e)` is a frame.** -/
instance : Order.Frame (G e) := Order.Frame.ofMinimalAxioms ⟨fun a S => by
  have hb : ∀ b ∈ S, a ⊓ b ≤ ⨆ b ∈ S, a ⊓ b := fun b hb =>
    le_iSup₂ (f := fun b (_ : b ∈ S) => a ⊓ b) b hb
  constructor
  · change a.V ⊓ (⨆ b ∈ S, b.V) ≤ _
    rw [inf_iSup₂_eq]
    exact iSup₂_le fun b hbS => (hb b hbS).1
  · change a.d ⊓ (⨆ b ∈ S, b.d) ≤ _
    rw [inf_iSup₂_eq]
    exact iSup₂_le fun b hbS => (hb b hbS).2⟩

theorem eq_bot_iff_V {x : G e} : x = ⊥ ↔ (x.V : Set ℝ) = ∅ := by
  constructor
  · rintro rfl
    rfl
  · intro h
    exact G.ext (Opens.ext h) (d_eq_bot_of_V h)

theorem bot_ne_top : (⊥ : G e) ≠ ⊤ := by
  intro h
  have : (1 / 2 : ℝ) ∈ ((⊤ : G e).V : Set ℝ) := ⟨by norm_num, by norm_num⟩
  rw [← h] at this
  exact this

end G

/-! ### The coordinate and the collar -/

/-- The endpoint value of `t^*(W)`: `e` if `0 ∈ W`, else `⊥`. -/
def endVal (e : P) (W : Opens ℝ) : P := ⨆ (_ : (0 : ℝ) ∈ W), e

theorem endVal_of_mem {e : P} {W : Opens ℝ} (h : (0 : ℝ) ∈ W) : endVal e W = e := iSup_pos h

theorem endVal_of_not_mem {e : P} {W : Opens ℝ} (h : (0 : ℝ) ∉ W) : endVal e W = ⊥ := iSup_neg h

/-- The underlying map of the coordinate. -/
def tHom' (e : P) (W : Opens ℝ) : G e where
  V := ⟨(W : Set ℝ) ∩ Ioo 0 1, W.isOpen.inter isOpen_Ioo⟩
  d := endVal e W
  hV := inter_subset_right
  hd := iSup_le fun _ => le_rfl
  glue := fun h => by
    have h0 : (0 : ℝ) ∈ W := by
      by_contra h0
      exact h (endVal_of_not_mem h0)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp W.isOpen 0 h0
    refine ⟨min ε 1, lt_min hε one_pos, fun t ht => ⟨hball ?_, ht.1, ht.2.trans_le (min_le_right _ _)⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact ht.2.trans_le (min_le_left _ _)

/-- **The coordinate `t : L_e → ℝ`**, by its inverse-image frame map. -/
def tHom (e : P) : FrameHom (Opens ℝ) (G e) where
  toFun := tHom' e
  map_inf' W W' := by
    apply G.ext
    · exact Opens.ext (by
        ext t
        exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, ⟨h2, h3⟩⟩, fun ⟨⟨h1, h3⟩, ⟨h2, _⟩⟩ => ⟨⟨h1, h2⟩, h3⟩⟩)
    · change endVal e (W ⊓ W') = endVal e W ⊓ endVal e W'
      by_cases h₁ : (0 : ℝ) ∈ W <;> by_cases h₂ : (0 : ℝ) ∈ W'
      · rw [endVal_of_mem h₁, endVal_of_mem h₂, endVal_of_mem (Opens.mem_inf.mpr ⟨h₁, h₂⟩),
          inf_idem]
      · rw [endVal_of_mem h₁, endVal_of_not_mem h₂,
          endVal_of_not_mem (fun h => h₂ (Opens.mem_inf.mp h).2), inf_bot_eq]
      · rw [endVal_of_not_mem h₁, endVal_of_not_mem (fun h => h₁ (Opens.mem_inf.mp h).1),
          bot_inf_eq]
      · rw [endVal_of_not_mem h₁, endVal_of_not_mem (fun h => h₁ (Opens.mem_inf.mp h).1),
          bot_inf_eq]
  map_top' := by
    apply G.ext
    · exact Opens.ext (by ext t; exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩)
    · exact endVal_of_mem (show (0 : ℝ) ∈ (⊤ : Opens ℝ) from trivial)
  map_sSup' S := by
    apply G.ext
    · apply Opens.ext
      ext t
      change t ∈ (sSup S : Opens ℝ) ∧ t ∈ Ioo (0:ℝ) 1 ↔ t ∈ (⨆ x ∈ _, G.V x : Opens ℝ)
      rw [Opens.mem_sSup]
      constructor
      · rintro ⟨⟨W, hW, htW⟩, ht⟩
        exact Opens.mem_iSup.mpr ⟨tHom' e W, Opens.mem_iSup.mpr ⟨⟨W, hW, rfl⟩, ⟨htW, ht⟩⟩⟩
      · intro h
        obtain ⟨x, hx⟩ := Opens.mem_iSup.mp h
        obtain ⟨⟨W, hW, rfl⟩, htW, ht⟩ := Opens.mem_iSup.mp hx
        exact ⟨⟨W, hW, htW⟩, ht⟩
    · change endVal e (sSup S) = ⨆ x ∈ _, G.d x
      rw [iSup_image]
      by_cases h : ∃ W ∈ S, (0 : ℝ) ∈ W
      · obtain ⟨W, hW, h0⟩ := h
        rw [endVal_of_mem (Opens.mem_sSup.mpr ⟨W, hW, h0⟩)]
        apply le_antisymm
        · exact le_iSup₂_of_le (f := fun W (_ : W ∈ S) => (tHom' e W).d) W hW
            (endVal_of_mem h0).ge
        · exact iSup₂_le fun W _ => iSup_le fun _ => le_rfl
      · rw [not_exists] at h
        rw [endVal_of_not_mem (fun h' => by
          obtain ⟨W, hW, h0⟩ := Opens.mem_sSup.mp h'
          exact h W ⟨hW, h0⟩)]
        refine (le_antisymm (iSup₂_le fun W hW => ?_) bot_le).symm
        exact (endVal_of_not_mem (fun h0 => h W ⟨hW, h0⟩)).le

@[simp] theorem tHom_V (e : P) (W : Opens ℝ) : ((tHom e W).V : Set ℝ) = (W : Set ℝ) ∩ Ioo 0 1 :=
  rfl

@[simp] theorem tHom_d (e : P) (W : Opens ℝ) : (tHom e W).d = endVal e W := rfl

/-- **The collar** `u_e = ((0, 1), ⊥)`. -/
def collar (e : P) : G e where
  V := ⟨Ioo 0 1, isOpen_Ioo⟩
  d := ⊥
  hV := subset_rfl
  hd := bot_le
  glue h := absurd rfl h

theorem tHom_Ioi_zero (e : P) : tHom e (oIoi 0) = collar e := by
  apply G.ext
  · exact Opens.ext (by ext t; exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩)
  · exact endVal_of_not_mem (show (0:ℝ) ∉ oIoi 0 from fun h => lt_irrefl (0:ℝ) h)

theorem collar_ne_top {e : P} (he : e ≠ ⊥) : collar e ≠ ⊤ := by
  intro h
  exact he (congrArg G.d h).symm

theorem tHom_Iio_one (e : P) : tHom e (oIio 1) = ⊤ := by
  apply G.ext
  · exact Opens.ext (by ext t; exact ⟨fun h => h.2, fun h => ⟨h.2, h⟩⟩)
  · exact endVal_of_mem (show (0 : ℝ) ∈ oIio 1 from (by norm_num : (0 : ℝ) < 1))

theorem tHom_Iio_zero (e : P) : tHom e (oIio 0) = ⊥ := by
  apply G.eq_bot_iff_V.mpr
  ext t
  simp only [tHom_V, coe_oIio, mem_inter_iff, mem_Iio, mem_Ioo, mem_empty_iff_false, iff_false]
  intro h
  linarith [h.1, h.2.1]

/-- A collar open with empty end: `(V, ⊥) = t^*(V)`. -/
theorem eq_tHom_of_d_eq_bot {x : G e} (h : x.d = ⊥) : x = tHom e x.V := by
  apply G.ext
  · exact Opens.ext (by ext t; simp only [tHom_V, mem_inter_iff]; exact ⟨fun ht => ⟨ht, x.hV ht⟩, fun ht => ht.1⟩)
  · rw [h, tHom_d, endVal_of_not_mem (fun h0 => lt_irrefl (0:ℝ) (x.hV h0).1)]

/-- The end-part open `D d = ((0, 1), d ⊓ e)`. -/
def Dopen (e : P) (d : P) : G e where
  V := ⟨Ioo 0 1, isOpen_Ioo⟩
  d := d ⊓ e
  hV := subset_rfl
  hd := inf_le_right
  glue _ := ⟨1, one_pos, subset_rfl⟩

theorem Dopen_inf (e a b : P) : Dopen e (a ⊓ b) = Dopen e a ⊓ Dopen e b := by
  apply G.ext
  · exact Opens.ext (by ext t; simp [Dopen])
  · change a ⊓ b ⊓ e = (a ⊓ e) ⊓ (b ⊓ e)
    rw [inf_inf_distrib_right]

theorem Dopen_mono (e : P) {a b : P} (h : a ≤ b) : Dopen e a ≤ Dopen e b :=
  ⟨le_rfl, show a ⊓ e ≤ b ⊓ e from inf_le_inf_right e h⟩

theorem Dopen_top (e : P) : Dopen e ⊤ = ⊤ := G.ext rfl (top_inf_eq e)

theorem Dopen_self (e : P) : Dopen e e = ⊤ := G.ext rfl (inf_idem e)

theorem Dopen_sSup_le (e : P) (S : Set P) :
    Dopen e (sSup S) ≤ collar e ⊔ ⨆ a ∈ S, Dopen e a := by
  constructor
  · exact le_sup_left
  · change sSup S ⊓ e ≤ ⊥ ⊔ (⨆ a ∈ S, Dopen e a).d
    rw [bot_sup_eq, sSup_inf_eq]
    refine iSup₂_le fun a ha => ?_
    have h1 : Dopen e a ≤ ⨆ a ∈ S, Dopen e a := le_iSup₂ (f := fun a (_ : a ∈ S) => Dopen e a) a ha
    exact h1.2

/-- **Decomposition of an open of `L_e`.** -/
theorem eq_decomp (x : G e) {ε : ℝ} (hε : 0 < ε) (hsub : Ioo 0 ε ⊆ (x.V : Set ℝ)) :
    x = tHom e x.V ⊔ (tHom e (oIio ε) ⊓ Dopen e x.d) := by
  apply G.ext
  · apply Opens.ext
    ext t
    simp only [G.V_sup, G.V_inf, Opens.coe_sup, Opens.coe_inf, tHom_V, coe_oIio, mem_union,
      mem_inter_iff, mem_Iio, mem_Ioo, Dopen, Opens.coe_mk]
    constructor
    · intro ht
      exact Or.inl ⟨ht, x.hV ht⟩
    · rintro (⟨ht, -⟩ | ⟨⟨htε, ht0, -⟩, -⟩)
      · exact ht
      · exact hsub ⟨ht0, htε⟩
  · change x.d = endVal e x.V ⊔ (endVal e (oIio ε) ⊓ (x.d ⊓ e))
    rw [endVal_of_not_mem (fun h0 => lt_irrefl (0:ℝ) (x.hV h0).1),
      endVal_of_mem (show (0:ℝ) ∈ oIio ε from hε), bot_sup_eq, inf_eq_left.mpr x.hd,
      inf_eq_right.mpr x.hd]

/-! ### Frame homomorphisms out of `O(L_e)` -/

variable {A : Type*} [Order.Frame A]

/-- Data defining a frame homomorphism out of `O(L_e)`: a real coordinate `σ`, valued in
`[0, 1)` at the end, and an endpoint map `δ`. -/
structure GlueData (e : P) (A : Type*) [Order.Frame A] where
  σ : FrameHom (Opens ℝ) A
  δ : P → A
  δ_inf : ∀ a b, δ (a ⊓ b) = δ a ⊓ δ b
  δ_sSup : ∀ S : Set P, δ (sSup S) ≤ σ (oIoi 0) ⊔ ⨆ a ∈ S, δ a
  δ_e : δ e = ⊤
  σ_Iio_one : σ (oIio 1) = ⊤

namespace GlueData

variable (D : GlueData e A)

theorem δ_mono {a b : P} (h : a ≤ b) : D.δ a ≤ D.δ b := by
  rw [← inf_eq_left.mpr h, D.δ_inf]
  exact inf_le_right

theorem δ_bot : D.δ ⊥ ≤ D.σ (oIoi 0) := by
  have := D.δ_sSup ∅
  rw [sSup_empty] at this
  simpa using this

/-- The value on an open `(V, d)`. -/
def toFun (x : G e) : A :=
  D.σ x.V ⊔ ⨆ (ε : ℝ) (_ : 0 < ε ∧ Ioo 0 ε ⊆ (x.V : Set ℝ)), D.σ (oIio ε) ⊓ D.δ x.d

theorem le_toFun_σ (x : G e) : D.σ x.V ≤ D.toFun x := le_sup_left

theorem le_toFun_ε (x : G e) {ε : ℝ} (hε : 0 < ε) (hsub : Ioo 0 ε ⊆ (x.V : Set ℝ)) :
    D.σ (oIio ε) ⊓ D.δ x.d ≤ D.toFun x :=
  le_sup_of_le_right (le_iSup₂_of_le (f := fun ε (_ : 0 < ε ∧ Ioo 0 ε ⊆ (x.V : Set ℝ)) =>
    D.σ (oIio ε) ⊓ D.δ x.d) ε ⟨hε, hsub⟩ le_rfl)

theorem toFun_mono {x y : G e} (h : x ≤ y) : D.toFun x ≤ D.toFun y := by
  apply sup_le
  · exact (fmono D.σ h.1).trans (D.le_toFun_σ y)
  · refine iSup₂_le fun ε hε => ?_
    exact (inf_le_inf le_rfl (D.δ_mono h.2)).trans
      (D.le_toFun_ε y hε.1 (hε.2.trans (SetLike.coe_subset_coe.mpr h.1)))

/-- `σ(-∞, ε) ⊓ σ(0, ∞) = σ(0, ε) ≤ σ(V)` when `(0, ε) ⊆ V`. -/
theorem σ_Iio_inf_Ioi_le {V : Opens ℝ} {ε : ℝ} (hsub : Ioo 0 ε ⊆ (V : Set ℝ)) :
    D.σ (oIio ε) ⊓ D.σ (oIoi 0) ≤ D.σ V := by
  rw [← map_inf]
  exact fmono D.σ (fun t ht => hsub ⟨ht.2, ht.1⟩)

theorem toFun_inf (x y : G e) : D.toFun (x ⊓ y) = D.toFun x ⊓ D.toFun y := by
  apply le_antisymm
  · exact le_inf (D.toFun_mono inf_le_left) (D.toFun_mono inf_le_right)
  set X := ⨆ (ε : ℝ) (_ : 0 < ε ∧ Ioo 0 ε ⊆ (x.V : Set ℝ)), D.σ (oIio ε) ⊓ D.δ x.d with hX
  set Y := ⨆ (ε : ℝ) (_ : 0 < ε ∧ Ioo 0 ε ⊆ (y.V : Set ℝ)), D.σ (oIio ε) ⊓ D.δ y.d with hY
  have h1 : D.σ x.V ⊓ D.σ y.V ≤ D.toFun (x ⊓ y) := by
    rw [← map_inf]
    exact D.le_toFun_σ (x ⊓ y)
  have h2 : X ⊓ D.σ y.V ≤ D.toFun (x ⊓ y) := by
    rw [hX, iSup_inf_eq]
    refine iSup_le fun ε => ?_
    rw [iSup_inf_eq]
    refine iSup_le fun hε => ?_
    refine (inf_le_inf_right _ inf_le_left).trans ?_
    rw [← map_inf]
    have hsub : oIio ε ⊓ y.V ≤ x.V ⊓ y.V := by
      intro t ht
      have h1 := (Opens.mem_inf.mp ht).1
      have h2 := (Opens.mem_inf.mp ht).2
      exact Opens.mem_inf.mpr ⟨hε.2 ⟨(y.hV h2).1, h1⟩, h2⟩
    exact (fmono D.σ hsub).trans (D.le_toFun_σ (x ⊓ y))
  have h3 : D.σ x.V ⊓ Y ≤ D.toFun (x ⊓ y) := by
    rw [hY, inf_iSup_eq]
    refine iSup_le fun ε => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun hε => ?_
    refine (inf_le_inf_left _ inf_le_left).trans ?_
    rw [← map_inf]
    have hsub : x.V ⊓ oIio ε ≤ x.V ⊓ y.V := by
      intro t ht
      have h1 := (Opens.mem_inf.mp ht).1
      have h2 := (Opens.mem_inf.mp ht).2
      exact Opens.mem_inf.mpr ⟨h1, hε.2 ⟨(x.hV h1).1, h2⟩⟩
    exact (fmono D.σ hsub).trans (D.le_toFun_σ (x ⊓ y))
  have h4 : X ⊓ Y ≤ D.toFun (x ⊓ y) := by
    rw [hX, iSup_inf_eq]
    refine iSup_le fun ε => ?_
    rw [iSup_inf_eq]
    refine iSup_le fun hε => ?_
    rw [hY, inf_iSup_eq]
    refine iSup_le fun ε' => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun hε' => ?_
    have hsub : Ioo 0 (min ε ε') ⊆ ((x ⊓ y).V : Set ℝ) := fun t ht =>
      ⟨hε.2 ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩, hε'.2 ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩⟩
    refine le_trans ?_ (D.le_toFun_ε (x ⊓ y) (lt_min hε.1 hε'.1) hsub)
    refine le_inf ?_ ?_
    · rcases le_total ε ε' with h | h
      · rw [min_eq_left h]; exact inf_le_left.trans inf_le_left
      · rw [min_eq_right h]; exact inf_le_right.trans inf_le_left
    · change _ ≤ D.δ (x.d ⊓ y.d)
      rw [D.δ_inf]
      exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  change (D.σ x.V ⊔ X) ⊓ (D.σ y.V ⊔ Y) ≤ D.toFun (x ⊓ y)
  rw [inf_sup_left, inf_sup_right, inf_sup_right]
  exact sup_le (sup_le h1 h2) (sup_le h3 h4)

theorem toFun_sSup_le (S : Set (G e)) : D.toFun (sSup S) ≤ ⨆ x ∈ S, D.toFun x := by
  have hσ : D.σ (sSup S).V ≤ ⨆ x ∈ S, D.toFun x := by
    rw [G.V_sSup, map_iSup₂]
    exact iSup₂_mono fun x _ => D.le_toFun_σ x
  apply sup_le hσ
  refine iSup₂_le fun ε hε => ?_
  -- `δ` of the join
  have hδ : D.δ (sSup S).d ≤ D.σ (oIoi 0) ⊔ ⨆ x ∈ S, D.δ x.d := by
    have := D.δ_sSup (G.d '' S)
    rw [sSup_image, iSup_image] at this
    exact this
  calc D.σ (oIio ε) ⊓ D.δ (sSup S).d
      ≤ D.σ (oIio ε) ⊓ (D.σ (oIoi 0) ⊔ ⨆ x ∈ S, D.δ x.d) := inf_le_inf_left _ hδ
    _ = (D.σ (oIio ε) ⊓ D.σ (oIoi 0)) ⊔ ⨆ x ∈ S, D.σ (oIio ε) ⊓ D.δ x.d := by
        rw [inf_sup_left, inf_iSup₂_eq]
    _ ≤ ⨆ x ∈ S, D.toFun x := by
        apply sup_le
        · exact (D.σ_Iio_inf_Ioi_le hε.2).trans hσ
        · refine iSup₂_le fun x hx => ?_
          by_cases hd : x.d = ⊥
          · rw [hd]
            refine ((inf_le_inf_left _ D.δ_bot).trans (D.σ_Iio_inf_Ioi_le hε.2)).trans hσ
          · obtain ⟨εx, hεx, hsubx⟩ := x.glue hd
            have hsplit : D.σ (oIio ε) ≤ D.σ (oIio εx) ⊔ D.σ (oIoo (εx / 2) ε) := by
              rw [← map_sup]
              refine fmono D.σ fun t (ht : t < ε) => ?_
              by_cases htx : t < εx
              · exact Or.inl htx
              · exact Or.inr ⟨by linarith [not_lt.mp htx], ht⟩
            have h2 : D.σ (oIoo (εx / 2) ε) ≤ D.σ (sSup S).V :=
              fmono D.σ fun t ht => hε.2 ⟨by linarith [ht.1], ht.2⟩
            calc D.σ (oIio ε) ⊓ D.δ x.d
                ≤ (D.σ (oIio εx) ⊔ D.σ (oIoo (εx / 2) ε)) ⊓ D.δ x.d := inf_le_inf_right _ hsplit
              _ ≤ (D.σ (oIio εx) ⊓ D.δ x.d) ⊔ D.σ (oIoo (εx / 2) ε) := by
                  rw [inf_sup_right]; exact sup_le_sup_left inf_le_left _
              _ ≤ ⨆ x ∈ S, D.toFun x := sup_le
                  ((D.le_toFun_ε x hεx hsubx).trans
                    (le_iSup₂ (f := fun x (_ : x ∈ S) => D.toFun x) x hx))
                  (h2.trans hσ)

/-- **The frame homomorphism defined by glue data.** -/
def toHom : FrameHom (G e) A where
  toFun := D.toFun
  map_inf' := D.toFun_inf
  map_top' := by
    apply top_unique
    refine le_trans ?_ (D.le_toFun_ε ⊤ one_pos subset_rfl)
    rw [D.σ_Iio_one, G.d_top, D.δ_e, inf_idem]
  map_sSup' S := by
    apply le_antisymm
    · rw [sSup_image]
      exact D.toFun_sSup_le S
    · exact sSup_le (by rintro _ ⟨x, hx, rfl⟩; exact D.toFun_mono (le_sSup hx))

@[simp] theorem toHom_apply (x : G e) : D.toHom x = D.toFun x := rfl

end GlueData

/-- The glue data of a frame homomorphism out of `O(L_e)`. -/
def GlueData.ofHom (h : FrameHom (G e) A) : GlueData e A where
  σ := h.comp (tHom e)
  δ d := h (Dopen e d)
  δ_inf a b := by rw [Dopen_inf, map_inf]
  δ_sSup S := by
    have := fmono h (Dopen_sSup_le e S)
    rw [map_sup, map_iSup₂, ← tHom_Ioi_zero] at this
    exact this
  δ_e := by rw [Dopen_self, map_top]
  σ_Iio_one := by
    change h (tHom e (oIio 1)) = ⊤
    rw [tHom_Iio_one, map_top]

theorem GlueData.toHom_ofHom (h : FrameHom (G e) A) : (GlueData.ofHom h).toHom = h := by
  ext x
  change (GlueData.ofHom h).toFun x = h x
  apply le_antisymm
  · apply sup_le
    · change h (tHom e x.V) ≤ h x
      refine fmono h ⟨fun t ht => ht.1, ?_⟩
      change endVal e x.V ≤ x.d
      rw [endVal_of_not_mem (fun h0 => lt_irrefl (0:ℝ) (x.hV h0).1)]
      exact bot_le
    · refine iSup₂_le fun ε hε => ?_
      change h (tHom e (oIio ε)) ⊓ h (Dopen e x.d) ≤ h x
      rw [← map_inf]
      refine fmono h ⟨fun t ht => hε.2 ⟨ht.1.2.1, ht.1.1⟩, ?_⟩
      exact inf_le_right.trans inf_le_left
  · by_cases hd : x.d = ⊥
    · conv_lhs => rw [eq_tHom_of_d_eq_bot hd]
      exact le_sup_left
    · obtain ⟨ε, hε, hsub⟩ := x.glue hd
      conv_lhs => rw [eq_decomp x hε hsub]
      rw [map_sup, map_inf]
      exact sup_le le_sup_left ((GlueData.ofHom h).le_toFun_ε x hε hsub)

/-- Postcomposition of glue data with a frame homomorphism. -/
def GlueData.mapHom {B : Type*} [Order.Frame B] (D : GlueData e A) (k : FrameHom A B) :
    GlueData e B where
  σ := k.comp D.σ
  δ d := k (D.δ d)
  δ_inf a b := by rw [D.δ_inf, map_inf]
  δ_sSup S := by
    have := fmono k (D.δ_sSup S)
    rw [map_sup, map_iSup₂] at this
    exact this
  δ_e := by rw [D.δ_e, map_top]
  σ_Iio_one := by
    change k (D.σ (oIio 1)) = ⊤
    rw [D.σ_Iio_one, map_top]

/-- **Naturality of the glued homomorphism.** -/
theorem GlueData.comp_toHom {B : Type*} [Order.Frame B] (D : GlueData e A) (k : FrameHom A B) :
    k.comp D.toHom = (D.mapHom k).toHom := by
  ext x
  change k (D.toFun x) = (D.mapHom k).toFun x
  simp only [GlueData.toFun, map_sup, map_iSup, map_inf]
  rfl

/-- **Frame homomorphisms out of `O(L_e)` are determined by `t^*` and `D`.** -/
theorem glue_ext {h h' : FrameHom (G e) A} (hσ : ∀ W, h (tHom e W) = h' (tHom e W))
    (hδ : ∀ d, h (Dopen e d) = h' (Dopen e d)) : h = h' := by
  rw [← GlueData.toHom_ofHom h, ← GlueData.toHom_ofHom h']
  have e1 : GlueData.ofHom h = GlueData.ofHom h' := by
    have hσ' : h.comp (tHom e) = h'.comp (tHom e) := FrameHom.ext hσ
    have hδ' : (fun d => h (Dopen e d)) = fun d => h' (Dopen e d) := funext hδ
    unfold GlueData.ofHom
    congr
  rw [e1]

/-! ### Points -/

/-- The collar point at `x ∈ (0, 1)`. -/
def collarPt (e : P) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : FrameHom (G e) Prop where
  toFun y := x ∈ y.V
  map_inf' _ _ := rfl
  map_top' := propext ⟨fun _ => trivial, fun _ => hx⟩
  map_sSup' S := by
    apply propext
    simp only [G.V_sSup, Opens.mem_iSup, sSup_Prop_eq, mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨_, ⟨y, hy, rfl⟩, hxy⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
      exact ⟨y, hy, hxy⟩

@[simp] theorem collarPt_apply (e : P) (x : ℝ) (hx) (y : G e) : collarPt e x hx y ↔ x ∈ y.V :=
  Iff.rfl

/-- **Every point of `L_e` is a collar point.** -/
theorem point_eq_collarPt (p : FrameHom (G e) Prop) :
    ∃ (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1), p = collarPt e x hx := by
  obtain ⟨x, hx⟩ := ptHom_surjective (p.comp (tHom e))
  have hval : ∀ W, p (tHom e W) ↔ x ∈ W := fun W => by
    have := congrArg (fun q : FrameHom (Opens ℝ) Prop => q W) hx
    exact Iff.of_eq this
  have hx1 : x < 1 := by
    have := (hval (oIio 1)).mp (by rw [tHom_Iio_one, map_top]; trivial)
    exact this
  have hx0 : 0 < x := by
    by_contra hle
    -- the point lies at the end: it would be a point of `P`
    have hu : ¬ p (collar e) := by
      rw [← tHom_Ioi_zero, hval]
      exact hle
    apply no_point (fun a => p (Dopen e a))
    · intro a b ha hb
      rw [Dopen_inf, map_inf]
      exact ⟨ha, hb⟩
    · intro a b hab ha
      exact fmono p (Dopen_mono e hab) ha
    · intro S hS
      have := fmono p (Dopen_sSup_le e S) hS
      rw [map_sup, map_iSup₂] at this
      rcases this with h | h
      · exact absurd h hu
      · simp only [iSup_Prop_eq] at h
        obtain ⟨a, ha, hpa⟩ := h
        exact ⟨a, ha, hpa⟩
    · rw [Dopen_top, map_top]
      trivial
  refine ⟨x, ⟨hx0, hx1⟩, ?_⟩
  ext y
  change p y ↔ x ∈ y.V
  have hu : p (collar e) := by
    rw [← tHom_Ioi_zero, hval]
    exact hx0
  have e1 : y ⊓ collar e = tHom e y.V := by
    apply G.ext
    · exact Opens.ext (by ext t; simp only [G.V_inf, Opens.coe_inf, tHom_V, mem_inter_iff, collar, Opens.coe_mk])
    · change y.d ⊓ ⊥ = endVal e y.V
      rw [inf_bot_eq, endVal_of_not_mem (fun h0 => lt_irrefl (0:ℝ) (y.hV h0).1)]
  constructor
  · intro hy
    have : p (y ⊓ collar e) := by rw [map_inf]; exact ⟨hy, hu⟩
    rw [e1, hval] at this
    exact this
  · intro hy
    have : p (y ⊓ collar e) := by rw [e1, hval]; exact hy
    rw [map_inf] at this
    exact this.1

/-- **Every nonzero open of `L_e` contains a point.** -/
theorem exists_point_of_ne_bot {y : G e} (hy : y ≠ ⊥) :
    ∃ p : FrameHom (G e) Prop, p y := by
  have : ((y.V : Set ℝ)).Nonempty := by
    by_contra h
    exact hy (G.eq_bot_iff_V.mpr (not_nonempty_iff_eq_empty.mp h))
  obtain ⟨x, hx⟩ := this
  exact ⟨collarPt e x (y.hV hx), hx⟩

/-- **`L_e` is connected**: complemented opens are trivial. -/
theorem G.eq_bot_or_eq_bot {y z : G e} (hinf : y ⊓ z = ⊥) (hsup : y ⊔ z = ⊤) :
    y = ⊥ ∨ z = ⊥ := by
  have hV1 : (y.V : Set ℝ) ∩ z.V = ∅ := by
    have := congrArg (fun w : G e => (w.V : Set ℝ)) hinf
    exact this
  have hV2 : (y.V : Set ℝ) ∪ z.V = Ioo 0 1 := by
    have := congrArg (fun w : G e => (w.V : Set ℝ)) hsup
    exact this
  have hpre : IsPreconnected (Ioo (0 : ℝ) 1) := isPreconnected_Ioo
  by_contra hne
  rw [not_or] at hne
  obtain ⟨a, ha⟩ : ((y.V : Set ℝ)).Nonempty := by
    by_contra h
    exact hne.1 (G.eq_bot_iff_V.mpr (not_nonempty_iff_eq_empty.mp h))
  obtain ⟨b, hb⟩ : ((z.V : Set ℝ)).Nonempty := by
    by_contra h
    exact hne.2 (G.eq_bot_iff_V.mpr (not_nonempty_iff_eq_empty.mp h))
  obtain ⟨c, -, hc1, hc2⟩ := hpre (y.V : Set ℝ) z.V y.V.isOpen z.V.isOpen hV2.symm.le
    ⟨a, y.hV ha, ha⟩ ⟨b, z.hV hb, hb⟩
  have : c ∈ (y.V : Set ℝ) ∩ z.V := ⟨hc1, hc2⟩
  rw [hV1] at this
  exact this

end PointlessEnd
