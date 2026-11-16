import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Real
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The real locale classifies frame-valued Dedekind cuts

For a frame `A`, a *cut model* in `A` is a pair of families `L, U : ℚ → A` of
two-sided Dedekind cuts with values in `A`: rounded, inhabited, disjoint and located
(TypeTopology's `DedekindReals.Type`, frame-valued).

**Theorem** (`cutEquiv`). Cut models in `A` correspond exactly to frame homomorphisms
`O(ℝ) → A`, that is, to locale maps from the locale of `A` to the real line:

* a frame homomorphism `h` gives `L q = h (q, ∞)` and `U q = h (-∞, q)`;
* a cut model gives `h W = ⨆ {L q ⊓ U r | (q, r) ⊆ W}`.

The second assignment preserves finite meets directly. It preserves arbitrary joins by a
compactness argument: a rational interval `[q', r']` inside a union of opens has a
Lebesgue number `δ`, and locatedness along a grid of mesh `< δ` (the *chain lemma*)
splits `L q' ⊓ U r'` into pieces `L s_k ⊓ U s_(k+2)`, each inside one of the opens.

The correspondence is natural in `A`. It is the frame-valued classifying property of the
real locale, proved without points: `A` may be the frame of a nonspatial locale.
For `A = Prop` it gives the points of the real locale: they are the real numbers
(`ptHom_surjective`).
-/

noncomputable section

open Set TopologicalSpace

namespace PointlessEnd

/-- Frame homomorphisms are monotone. -/
theorem fmono {α β : Type*} [CompleteLattice α] [CompleteLattice β] (f : FrameHom α β) {a b : α}
    (h : a ≤ b) : f a ≤ f b :=
  OrderHomClass.mono f h

/-! ### Rational intervals as opens -/

/-- `(x, ∞)`. -/
def oIoi (x : ℝ) : Opens ℝ := ⟨Ioi x, isOpen_Ioi⟩

/-- `(-∞, x)`. -/
def oIio (x : ℝ) : Opens ℝ := ⟨Iio x, isOpen_Iio⟩

/-- `(x, y)`. -/
def oIoo (x y : ℝ) : Opens ℝ := ⟨Ioo x y, isOpen_Ioo⟩

@[simp] theorem coe_oIoi (x : ℝ) : (oIoi x : Set ℝ) = Ioi x := rfl
@[simp] theorem coe_oIio (x : ℝ) : (oIio x : Set ℝ) = Iio x := rfl
@[simp] theorem coe_oIoo (x y : ℝ) : (oIoo x y : Set ℝ) = Ioo x y := rfl

theorem oIoi_inf_oIio (x y : ℝ) : oIoi x ⊓ oIio y = oIoo x y := Opens.ext rfl

/-- Every open of `ℝ` is the union of the rational intervals it contains. -/
theorem opens_eq_iSup_oIoo (W : Opens ℝ) :
    W = ⨆ (q : ℚ) (r : ℚ) (_ : Ioo (q : ℝ) r ⊆ W), oIoo q r := by
  apply le_antisymm
  · intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp W.isOpen x hx
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x - ε < x by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show x < x + ε by linarith)
    have hsub : Ioo (q : ℝ) r ⊆ W := fun y hy => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2])
    simp only [Opens.mem_iSup]
    exact ⟨q, r, hsub, hq2, hr1⟩
  · exact iSup_le fun q => iSup_le fun r => iSup_le fun h => h

/-! ### Cut models -/

variable {A B : Type*} [Order.Frame A] [Order.Frame B]

/-- **Frame-valued two-sided Dedekind cuts.** -/
@[ext] structure CutModel (A : Type*) [Order.Frame A] where
  /-- The lower cut: `L q` is where `q < x`. -/
  L : ℚ → A
  /-- The upper cut: `U q` is where `x < q`. -/
  U : ℚ → A
  roundedL : ∀ q, L q = ⨆ (r : ℚ) (_ : q < r), L r
  roundedU : ∀ q, U q = ⨆ (r : ℚ) (_ : r < q), U r
  inhabitedL : ⨆ q, L q = ⊤
  inhabitedU : ⨆ q, U q = ⊤
  disjoint : ∀ q, L q ⊓ U q = ⊥
  located : ∀ q r, q < r → L q ⊔ U r = ⊤

namespace CutModel

variable (c : CutModel A)

theorem L_anti {q r : ℚ} (h : q ≤ r) : c.L r ≤ c.L q := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · rw [c.roundedL q]
    exact le_iSup₂ (f := fun r (_ : q < r) => c.L r) r h

theorem U_mono {q r : ℚ} (h : q ≤ r) : c.U q ≤ c.U r := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · rw [c.roundedU r]
    exact le_iSup₂ (f := fun q (_ : q < r) => c.U q) q h

theorem L_inf_U_of_le {q r : ℚ} (h : r ≤ q) : c.L q ⊓ c.U r = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf (c.L_anti h) le_rfl).trans (c.disjoint r).le)

/-- **The chain lemma.** Along a strictly increasing sequence of rationals, locatedness
splits `L s_m ⊓ U s_(m+n+2)` into the overlapping windows `L s_k ⊓ U s_(k+2)`. -/
theorem chain (s : ℕ → ℚ) (hs : StrictMono s) : ∀ n m,
    c.L (s m) ⊓ c.U (s (m + n + 2)) ≤
      ⨆ (k : ℕ) (_ : m ≤ k ∧ k ≤ m + n), c.L (s k) ⊓ c.U (s (k + 2)) := by
  intro n
  induction n with
  | zero =>
    intro m
    exact le_iSup₂_of_le (f := fun k (_ : m ≤ k ∧ k ≤ m + 0) => c.L (s k) ⊓ c.U (s (k + 2)))
      m ⟨le_rfl, by omega⟩ le_rfl
  | succ n ih =>
    intro m
    have hloc := c.located (s (m + 1)) (s (m + 2)) (hs (by omega))
    have e : m + (n + 1) + 2 = (m + 1) + n + 2 := by omega
    rw [e]
    calc c.L (s m) ⊓ c.U (s (m + 1 + n + 2))
        = c.L (s m) ⊓ c.U (s (m + 1 + n + 2)) ⊓ (c.L (s (m + 1)) ⊔ c.U (s (m + 2))) := by
          rw [hloc, inf_top_eq]
      _ = (c.L (s m) ⊓ c.U (s (m + 1 + n + 2)) ⊓ c.L (s (m + 1))) ⊔
            (c.L (s m) ⊓ c.U (s (m + 1 + n + 2)) ⊓ c.U (s (m + 2))) := inf_sup_left _ _ _
      _ ≤ (c.L (s (m + 1)) ⊓ c.U (s (m + 1 + n + 2))) ⊔ (c.L (s m) ⊓ c.U (s (m + 2))) :=
          sup_le_sup (le_inf inf_le_right (inf_le_left.trans inf_le_right))
            (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      _ ≤ ⨆ (k : ℕ) (_ : m ≤ k ∧ k ≤ m + (n + 1)), c.L (s k) ⊓ c.U (s (k + 2)) := by
          apply sup_le
          · refine (ih (m + 1)).trans (iSup₂_le fun k hk => ?_)
            exact le_iSup₂_of_le (f := fun k (_ : m ≤ k ∧ k ≤ m + (n + 1)) =>
              c.L (s k) ⊓ c.U (s (k + 2))) k ⟨by omega, by omega⟩ le_rfl
          · exact le_iSup₂_of_le (f := fun k (_ : m ≤ k ∧ k ≤ m + (n + 1)) =>
              c.L (s k) ⊓ c.U (s (k + 2))) m ⟨le_rfl, by omega⟩ le_rfl

/-- The value of a cut model on an open set. -/
def toFun (W : Opens ℝ) : A := ⨆ (q : ℚ) (r : ℚ) (_ : Ioo (q : ℝ) r ⊆ W), c.L q ⊓ c.U r

theorem le_toFun {W : Opens ℝ} {q r : ℚ} (h : Ioo (q : ℝ) r ⊆ W) : c.L q ⊓ c.U r ≤ c.toFun W :=
  le_iSup_of_le q (le_iSup_of_le r (le_iSup_of_le h le_rfl))

theorem toFun_mono {W W' : Opens ℝ} (h : W ≤ W') : c.toFun W ≤ c.toFun W' :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun hqr => c.le_toFun (hqr.trans h)

/-- `L q ⊓ U r = ⨆ L q' ⊓ U r'` over `q < q'`, `r' < r`. -/
theorem L_inf_U_le (q r : ℚ) :
    c.L q ⊓ c.U r ≤ ⨆ (q' : ℚ) (_ : q < q') (r' : ℚ) (_ : r' < r), c.L q' ⊓ c.U r' := by
  conv_lhs => rw [c.roundedL q, c.roundedU r]
  rw [iSup_inf_eq]
  refine iSup_le fun q' => ?_
  rw [iSup_inf_eq]
  refine iSup_le fun hq' => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun r' => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun hr' => ?_
  exact le_iSup₂_of_le (f := fun q' (_ : q < q') => ⨆ (r' : ℚ) (_ : r' < r), c.L q' ⊓ c.U r')
    q' hq' (le_iSup₂_of_le (f := fun r' (_ : r' < r) => c.L q' ⊓ c.U r') r' hr' le_rfl)

theorem inf_four_le (q r q' r' : ℚ) :
    (c.L q ⊓ c.U r) ⊓ (c.L q' ⊓ c.U r') ≤ c.L (max q q') ⊓ c.U (min r r') := by
  refine le_inf ?_ ?_
  · rcases le_total q q' with h | h
    · rw [max_eq_right h]; exact inf_le_right.trans inf_le_left
    · rw [max_eq_left h]; exact inf_le_left.trans inf_le_left
  · rcases le_total r r' with h | h
    · rw [min_eq_left h]; exact inf_le_left.trans inf_le_right
    · rw [min_eq_right h]; exact inf_le_right.trans inf_le_right

/-- **Joins.** The key compactness step. -/
theorem toFun_sSup_le (S : Set (Opens ℝ)) : c.toFun (sSup S) ≤ ⨆ W ∈ S, c.toFun W := by
  refine iSup_le fun q => iSup_le fun r => iSup_le fun hqr => ?_
  refine (c.L_inf_U_le q r).trans ?_
  refine iSup₂_le fun q' hq' => iSup₂_le fun r' hr' => ?_
  rcases le_or_gt r' q' with hle | hlt
  · rw [c.L_inf_U_of_le hle]
    exact bot_le
  -- the compact interval `[q', r']` inside the union of `S`
  have hcover : Icc (q' : ℝ) r' ⊆ ⋃ i : S, (i.1 : Set ℝ) := by
    intro x hx
    have hx' : x ∈ (sSup S : Opens ℝ) := hqr ⟨lt_of_lt_of_le (by exact_mod_cast hq') hx.1,
      lt_of_le_of_lt hx.2 (by exact_mod_cast hr')⟩
    rw [Opens.mem_sSup] at hx'
    obtain ⟨W, hW, hxW⟩ := hx'
    exact mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun i : S => i.1.isOpen) hcover
  -- a grid of mesh `< δ`
  obtain ⟨N, hN⟩ := exists_nat_gt (((r' : ℝ) - q') / δ)
  set M : ℕ := N + 2 with hM
  have hMpos : (0 : ℚ) < M := by positivity
  set h : ℚ := (r' - q') / M with hh
  have hhpos : 0 < h := div_pos (sub_pos.mpr hlt) hMpos
  have hhδ : (h : ℝ) < δ := by
    rw [hh]
    push_cast
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < M)]
    have h1 : ((r' : ℝ) - q') / δ < M := lt_of_lt_of_le hN (by rw [hM]; push_cast; linarith)
    rw [div_lt_iff₀ hδ] at h1
    linarith
  let s : ℕ → ℚ := fun k => q' + k * h
  have hs : StrictMono s := fun a b hab => by
    simp only [s]
    have : (a : ℚ) < b := by exact_mod_cast hab
    nlinarith
  have hs0 : s 0 = q' := by simp [s]
  have hsM : s M = r' := by
    simp only [s, hh]
    field_simp
    ring
  have hchain := c.chain s hs N 0
  have e : 0 + N + 2 = M := by omega
  rw [e, hs0, hsM] at hchain
  refine hchain.trans (iSup₂_le fun k hk => ?_)
  -- the window around `s (k+1)` lies in one member of `S`
  have hk1 : ((s (k + 1) : ℚ) : ℝ) ∈ Icc (q' : ℝ) r' := by
    simp only [s, mem_Icc]
    push_cast
    constructor
    · have : (0 : ℝ) ≤ ((k : ℝ) + 1) * h := by positivity
      linarith
    · have hkM : (k : ℝ) + 1 ≤ M := by
        have : k + 1 ≤ M := by omega
        exact_mod_cast this
      have hr : ((r' : ℚ) : ℝ) = (q' : ℝ) + (M : ℝ) * (h : ℝ) := by
        rw [← hsM]; simp only [s]; push_cast; ring
      rw [hr]
      have : ((k : ℝ) + 1) * h ≤ M * h := mul_le_mul_of_nonneg_right hkM (by positivity)
      linarith
  obtain ⟨⟨W, hW⟩, hball⟩ := hleb _ hk1
  have hwin : Ioo ((s k : ℚ) : ℝ) (s (k + 2)) ⊆ W := by
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    simp only [s] at hy ⊢
    push_cast at hy ⊢
    constructor <;> nlinarith [hy.1, hy.2]
  exact (c.le_toFun hwin).trans (le_iSup₂_of_le (f := fun W (_ : W ∈ S) => c.toFun W) W hW le_rfl)

/-- **A cut model is a frame homomorphism `O(ℝ) → A`.** -/
def toHom : FrameHom (Opens ℝ) A where
  toFun := c.toFun
  map_inf' W W' := by
    apply le_antisymm
    · exact le_inf (c.toFun_mono inf_le_left) (c.toFun_mono inf_le_right)
    · change c.toFun W ⊓ c.toFun W' ≤ c.toFun (W ⊓ W')
      unfold toFun
      rw [iSup_inf_eq]; refine iSup_le fun q => ?_
      rw [iSup_inf_eq]; refine iSup_le fun r => ?_
      rw [iSup_inf_eq]; refine iSup_le fun hW => ?_
      rw [inf_iSup_eq]; refine iSup_le fun q' => ?_
      rw [inf_iSup_eq]; refine iSup_le fun r' => ?_
      rw [inf_iSup_eq]; refine iSup_le fun hW' => ?_
      refine (c.inf_four_le q r q' r').trans (c.le_toFun ?_)
      · intro x hx
        simp only [mem_Ioo] at hx
        push_cast at hx
        simp only [max_lt_iff, lt_min_iff] at hx
        exact ⟨hW ⟨hx.1.1, hx.2.1⟩, hW' ⟨hx.1.2, hx.2.2⟩⟩
  map_top' := by
    apply top_unique
    calc (⊤ : A) = (⨆ q, c.L q) ⊓ (⨆ r, c.U r) := by rw [c.inhabitedL, c.inhabitedU, inf_top_eq]
      _ ≤ c.toFun ⊤ := by
        rw [iSup_inf_eq]
        refine iSup_le fun q => ?_
        rw [inf_iSup_eq]
        exact iSup_le fun r => c.le_toFun (fun _ _ => trivial)
  map_sSup' S := by
    apply le_antisymm
    · rw [sSup_image]
      exact c.toFun_sSup_le S
    · exact sSup_le (by rintro _ ⟨W, hW, rfl⟩; exact c.toFun_mono (le_sSup hW))

@[simp] theorem toHom_apply (W : Opens ℝ) : c.toHom W = c.toFun W := rfl

/-- Frame homomorphisms `O(ℝ) → A` give cut models. -/
def ofHom (h : FrameHom (Opens ℝ) A) : CutModel A where
  L q := h (oIoi q)
  U q := h (oIio q)
  roundedL q := by
    rw [← map_iSup₂ h]
    congr 1
    apply le_antisymm
    · intro x (hx : (q : ℝ) < x)
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hx
      simp only [Opens.mem_iSup]
      exact ⟨r, by exact_mod_cast hr1, hr2⟩
    · refine iSup₂_le fun r hr => ?_
      intro x (hx : (r : ℝ) < x)
      exact lt_trans (by exact_mod_cast hr) hx
  roundedU q := by
    rw [← map_iSup₂ h]
    congr 1
    apply le_antisymm
    · intro x (hx : x < (q : ℝ))
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hx
      simp only [Opens.mem_iSup]
      exact ⟨r, by exact_mod_cast hr2, hr1⟩
    · refine iSup₂_le fun r hr => ?_
      intro x (hx : x < (r : ℝ))
      exact lt_trans hx (by exact_mod_cast hr)
  inhabitedL := by
    rw [← map_iSup h, ← map_top h]
    congr 1
    apply top_unique
    intro x _
    obtain ⟨r, -, hr⟩ := exists_rat_btwn (show x - 1 < x by linarith)
    simp only [Opens.mem_iSup]
    exact ⟨r, hr⟩
  inhabitedU := by
    rw [← map_iSup h, ← map_top h]
    congr 1
    apply top_unique
    intro x _
    obtain ⟨r, hr, -⟩ := exists_rat_btwn (show x < x + 1 by linarith)
    simp only [Opens.mem_iSup]
    exact ⟨r, hr⟩
  disjoint q := by
    rw [← map_inf h, ← map_bot h]
    congr 1
    refine le_antisymm (fun x hx => ?_) bot_le
    exact absurd ((show (q : ℝ) < x from hx.1).trans hx.2) (lt_irrefl _)
  located q r hqr := by
    rw [← map_sup h, ← map_top h]
    congr 1
    apply top_unique
    intro x _
    by_cases hx : (q : ℝ) < x
    · exact Or.inl hx
    · exact Or.inr (lt_of_le_of_lt (not_lt.mp hx) (by exact_mod_cast hqr))

@[simp] theorem ofHom_L (h : FrameHom (Opens ℝ) A) (q : ℚ) : (ofHom h).L q = h (oIoi q) := rfl

@[simp] theorem ofHom_U (h : FrameHom (Opens ℝ) A) (q : ℚ) : (ofHom h).U q = h (oIio q) := rfl

theorem toHom_ofHom (h : FrameHom (Opens ℝ) A) : (ofHom h).toHom = h := by
  ext W
  change (ofHom h).toFun W = h W
  conv_rhs => rw [opens_eq_iSup_oIoo W]
  simp only [toFun, ofHom_L, ofHom_U, map_iSup, ← map_inf, oIoi_inf_oIio]

theorem ofHom_toHom : ofHom c.toHom = c := by
  ext q : 2
  · change c.toFun (oIoi q) = c.L q
    apply le_antisymm
    · refine iSup_le fun q' => iSup_le fun r' => iSup_le fun h => ?_
      rcases le_or_gt r' q' with hle | hlt
      · rw [c.L_inf_U_of_le hle]; exact bot_le
      · have hq : q ≤ q' := by
          by_contra hlt'
          rw [not_le] at hlt'
          obtain ⟨x, hx1, hx2⟩ := exists_between (show (q' : ℝ) < min (q : ℝ) r' from
            lt_min (by exact_mod_cast hlt') (by exact_mod_cast hlt))
          have := h ⟨hx1, lt_of_lt_of_le hx2 (min_le_right _ _)⟩
          exact absurd (lt_of_lt_of_le this (le_of_lt (lt_of_lt_of_le hx2 (min_le_left _ _))))
            (lt_irrefl _)
        exact inf_le_left.trans (c.L_anti hq)
    · rw [c.roundedL q]
      refine iSup₂_le fun q' hq' => ?_
      calc c.L q' = c.L q' ⊓ ⨆ r, c.U r := by rw [c.inhabitedU, inf_top_eq]
        _ = ⨆ r, c.L q' ⊓ c.U r := inf_iSup_eq _ _
        _ ≤ c.toFun (oIoi q) := iSup_le fun r => c.le_toFun fun x hx =>
            lt_trans (by exact_mod_cast hq') hx.1
  · change c.toFun (oIio q) = c.U q
    apply le_antisymm
    · refine iSup_le fun q' => iSup_le fun r' => iSup_le fun h => ?_
      rcases le_or_gt r' q' with hle | hlt
      · rw [c.L_inf_U_of_le hle]; exact bot_le
      · have hr : r' ≤ q := by
          by_contra hlt'
          rw [not_le] at hlt'
          obtain ⟨x, hx1, hx2⟩ := exists_between (show max (q : ℝ) q' < r' from
            max_lt (by exact_mod_cast hlt') (by exact_mod_cast hlt))
          have := h ⟨lt_of_le_of_lt (le_max_right _ _) hx1, hx2⟩
          exact absurd (lt_of_le_of_lt (le_max_left _ _) hx1) (not_lt.mpr (le_of_lt this))
        exact inf_le_right.trans (c.U_mono hr)
    · rw [c.roundedU q]
      refine iSup₂_le fun r hr => ?_
      calc c.U r = (⨆ q', c.L q') ⊓ c.U r := by rw [c.inhabitedL, top_inf_eq]
        _ = ⨆ q', c.L q' ⊓ c.U r := iSup_inf_eq _ _
        _ ≤ c.toFun (oIio q) := iSup_le fun q' => c.le_toFun fun x hx =>
            lt_trans hx.2 (by exact_mod_cast hr)

end CutModel

/-- **The classifying property of the real locale.** -/
def cutEquiv : CutModel A ≃ FrameHom (Opens ℝ) A where
  toFun c := c.toHom
  invFun h := CutModel.ofHom h
  left_inv c := c.ofHom_toHom
  right_inv h := CutModel.toHom_ofHom h

/-- Two frame homomorphisms `O(ℝ) → A` agreeing on all rational half-lines are equal. -/
theorem frameHom_ext_rat {h h' : FrameHom (Opens ℝ) A} (hL : ∀ q : ℚ, h (oIoi q) = h' (oIoi q))
    (hU : ∀ q : ℚ, h (oIio q) = h' (oIio q)) : h = h' := by
  rw [← CutModel.toHom_ofHom h, ← CutModel.toHom_ofHom h']
  congr 1
  ext q : 2
  · exact hL q
  · exact hU q

/-! ### Naturality -/

namespace CutModel

/-- Transport of a cut model along a frame homomorphism. -/
def map (k : FrameHom A B) (c : CutModel A) : CutModel B :=
  ofHom (k.comp c.toHom)

@[simp] theorem map_L (k : FrameHom A B) (c : CutModel A) (q : ℚ) : (c.map k).L q = k (c.L q) := by
  change k (c.toHom (oIoi q)) = _
  conv_rhs => rw [← c.ofHom_toHom]
  rfl

@[simp] theorem map_U (k : FrameHom A B) (c : CutModel A) (q : ℚ) : (c.map k).U q = k (c.U q) := by
  change k (c.toHom (oIio q)) = _
  conv_rhs => rw [← c.ofHom_toHom]
  rfl

theorem toHom_map (k : FrameHom A B) (c : CutModel A) : (c.map k).toHom = k.comp c.toHom :=
  toHom_ofHom _

end CutModel

/-! ### Points of the real locale -/

/-- The point of the real locale at `x`. -/
def ptHom (x : ℝ) : FrameHom (Opens ℝ) Prop where
  toFun W := x ∈ W
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' S := by
    apply propext
    rw [Opens.mem_sSup]
    simp only [sSup_Prop_eq, mem_image]
    constructor
    · rintro ⟨W, hW, hx⟩
      exact ⟨_, ⟨W, hW, rfl⟩, hx⟩
    · rintro ⟨_, ⟨W, hW, rfl⟩, hx⟩
      exact ⟨W, hW, hx⟩

@[simp] theorem ptHom_apply (x : ℝ) (W : Opens ℝ) : ptHom x W ↔ x ∈ W := Iff.rfl

theorem ptHom_injective : Function.Injective ptHom := by
  intro x y h
  by_contra hne
  have := congrArg (fun p : FrameHom (Opens ℝ) Prop => p (oIoo (x - |x - y|) (x + |x - y|))) h
  simp only [ptHom_apply] at this
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hx : x - |x - y| < x ∧ x < x + |x - y| := ⟨by linarith, by linarith⟩
  have hy := (Opens.mem_mk.mp (this.mp hx))
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonpos (by linarith)] at hy; linarith [hy.2]
  · rw [abs_of_nonneg (by linarith)] at hy; linarith [hy.1]

/-- **Points of the real locale are real numbers** (sobriety of `ℝ`, via cuts). -/
theorem ptHom_surjective (p : FrameHom (Opens ℝ) Prop) : ∃ x, p = ptHom x := by
  let c := CutModel.ofHom p
  have hL : ∃ q : ℚ, c.L q := by
    have h : (⨆ q, c.L q : Prop) := by rw [c.inhabitedL]; trivial
    rwa [iSup_Prop_eq] at h
  have hU : ∃ r : ℚ, c.U r := by
    have h : (⨆ q, c.U q : Prop) := by rw [c.inhabitedU]; trivial
    rwa [iSup_Prop_eq] at h
  obtain ⟨r₀, hr₀⟩ := hU
  have hbound : ∀ q : ℚ, c.L q → q < r₀ := by
    intro q hq
    by_contra hle
    rw [not_lt] at hle
    have := c.L_inf_U_of_le hle
    have h2 : (c.L q ⊓ c.U r₀ : Prop) := ⟨hq, hr₀⟩
    rw [this] at h2
    exact h2
  let T : Set ℝ := {y | ∃ q : ℚ, c.L q ∧ y = q}
  have hTne : T.Nonempty := by
    obtain ⟨q, hq⟩ := hL
    exact ⟨q, q, hq, rfl⟩
  have hTbdd : BddAbove T := ⟨r₀, by
    rintro _ ⟨q, hq, rfl⟩
    exact le_of_lt (by exact_mod_cast hbound q hq)⟩
  set x := sSup T with hx
  -- the lower cut is `q < x`
  have hLiff : ∀ q : ℚ, c.L q ↔ (q : ℝ) < x := by
    intro q
    constructor
    · intro hq
      have hr := c.roundedL q
      have hq' : (⨆ (r : ℚ) (_ : q < r), c.L r : Prop) := hr ▸ hq
      simp only [iSup_Prop_eq] at hq'
      obtain ⟨r, hqr, hr⟩ := hq'
      exact lt_of_lt_of_le (by exact_mod_cast hqr) (le_csSup hTbdd ⟨r, hr, rfl⟩)
    · intro hq
      obtain ⟨_, ⟨r, hr, rfl⟩, hqr⟩ := exists_lt_of_lt_csSup hTne hq
      exact c.L_anti (le_of_lt (by exact_mod_cast hqr)) hr
  -- the upper cut is `x < q`
  have hUiff : ∀ q : ℚ, c.U q ↔ x < q := by
    intro q
    constructor
    · intro hq
      have hr := c.roundedU q
      have hq' : (⨆ (r : ℚ) (_ : r < q), c.U r : Prop) := hr ▸ hq
      simp only [iSup_Prop_eq] at hq'
      obtain ⟨r, hrq, hr⟩ := hq'
      have hle : x ≤ (r : ℝ) := by
        refine csSup_le hTne ?_
        rintro _ ⟨q', hq', rfl⟩
        by_contra hlt
        rw [not_le] at hlt
        have := c.L_inf_U_of_le (le_of_lt (by exact_mod_cast hlt : r < q'))
        have h2 : (c.L q' ⊓ c.U r : Prop) := ⟨hq', hr⟩
        rw [this] at h2
        exact h2
      exact lt_of_le_of_lt hle (by exact_mod_cast hrq)
    · intro hq
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hq
      have hloc := c.located r q (by exact_mod_cast hr2)
      have h2 : (c.L r ⊔ c.U q : Prop) := by rw [hloc]; trivial
      rcases h2 with h2 | h2
      · exact absurd ((hLiff r).mp h2) (not_lt.mpr (le_of_lt hr1))
      · exact h2
  refine ⟨x, ?_⟩
  rw [← CutModel.toHom_ofHom p]
  ext W
  change c.toFun W ↔ x ∈ W
  simp only [CutModel.toFun, iSup_Prop_eq]
  constructor
  · rintro ⟨q, r, hW, hq, hr⟩
    exact hW ⟨(hLiff q).mp hq, (hUiff r).mp hr⟩
  · intro hxW
    have := opens_eq_iSup_oIoo W
    have hxW' : x ∈ (⨆ (q : ℚ) (r : ℚ) (_ : Ioo (q : ℝ) r ⊆ W), oIoo q r : Opens ℝ) := by
      rw [← this]; exact hxW
    simp only [Opens.mem_iSup] at hxW'
    obtain ⟨q, r, hW, hq, hr⟩ := hxW'
    exact ⟨q, r, hW, (hLiff q).mpr hq, (hUiff r).mpr hr⟩

/-! ### The maximum of two cuts -/

namespace CutModel

/-- **The maximum of two frame-valued cuts**: `q < max x y` iff `q < x ∨ q < y`, and
`max x y < q` iff `x < q ∧ y < q`. -/
def max (c d : CutModel A) : CutModel A where
  L q := c.L q ⊔ d.L q
  U q := c.U q ⊓ d.U q
  roundedL q := by
    apply le_antisymm
    · apply sup_le
      · rw [c.roundedL q]
        exact iSup₂_mono fun r _ => le_sup_left
      · rw [d.roundedL q]
        exact iSup₂_mono fun r _ => le_sup_right
    · exact iSup₂_le fun r hr => sup_le_sup (c.L_anti hr.le) (d.L_anti hr.le)
  roundedU q := by
    apply le_antisymm
    · conv_lhs => rw [c.roundedU q, d.roundedU q]
      rw [iSup₂_inf_eq]
      refine iSup₂_le fun r hr => ?_
      rw [inf_iSup₂_eq]
      refine iSup₂_le fun r' hr' => ?_
      refine le_iSup₂_of_le (f := fun r (_ : r < q) => c.U r ⊓ d.U r) (Max.max r r')
        (max_lt hr hr') ?_
      exact inf_le_inf (c.U_mono (le_max_left _ _)) (d.U_mono (le_max_right _ _))
    · exact iSup₂_le fun r hr => inf_le_inf (c.U_mono hr.le) (d.U_mono hr.le)
  inhabitedL := top_unique (c.inhabitedL.ge.trans (iSup_mono fun q => le_sup_left))
  inhabitedU := by
    apply top_unique
    calc (⊤ : A) = (⨆ q, c.U q) ⊓ (⨆ r, d.U r) := by rw [c.inhabitedU, d.inhabitedU, inf_top_eq]
      _ ≤ ⨆ q, c.U q ⊓ d.U q := by
          rw [iSup_inf_eq]
          refine iSup_le fun q => ?_
          rw [inf_iSup_eq]
          refine iSup_le fun r => ?_
          exact le_iSup_of_le (Max.max q r)
            (inf_le_inf (c.U_mono (le_max_left _ _)) (d.U_mono (le_max_right _ _)))
  disjoint q := by
    apply le_bot_iff.mp
    rw [inf_sup_right]
    apply sup_le
    · exact (inf_le_inf_left _ inf_le_left).trans (c.disjoint q).le
    · exact (inf_le_inf_left _ inf_le_right).trans (d.disjoint q).le
  located q r hqr := by
    apply top_unique
    rw [sup_inf_left]
    refine le_inf ?_ ?_
    · rw [sup_right_comm, c.located q r hqr, top_sup_eq]
    · rw [sup_assoc, d.located q r hqr, sup_top_eq]

@[simp] theorem max_L (c d : CutModel A) (q : ℚ) : (c.max d).L q = c.L q ⊔ d.L q := rfl

@[simp] theorem max_U (c d : CutModel A) (q : ℚ) : (c.max d).U q = c.U q ⊓ d.U q := rfl

/-- The maximum is natural. -/
theorem max_map (k : FrameHom A B) (c d : CutModel A) : (c.max d).map k = (c.map k).max (d.map k) := by
  ext q : 2
  · simp [map_sup]
  · simp [map_inf]

/-- Values of a cut model's frame homomorphism on half-lines. -/
theorem toHom_oIoi (c : CutModel A) (q : ℚ) : c.toHom (oIoi q) = c.L q := by
  conv_rhs => rw [← c.ofHom_toHom]
  rfl

theorem toHom_oIio (c : CutModel A) (q : ℚ) : c.toHom (oIio q) = c.U q := by
  conv_rhs => rw [← c.ofHom_toHom]
  rfl

end CutModel

end PointlessEnd
