import RealContinuity.LongRay
import RealContinuity.EndpointCharts
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.SuccPred.Limit

/-!
# Real charts on the closed long ray

For a countable ordinal `b`, the initial segment `[0, (b,0))` of the long ray
is order-isomorphic to a real interval `[0, S_b)`. The isomorphism is the
weighted sum: choose an injection `e : Iio b → ℕ`, give the unit interval
indexed by `a < b` the weight `w a = (1/2)^(e a)`, and send `(a, t)` to
`F a + t · w a` where `F a = Σ_{c < a} w c`.

The resulting coordinate `Φ_b : L → [0, S_b]` is monotone and continuous on
all of `L` (constant `S_b` from `(b,0)` on), and its inverse on `[0, S_b)` is
continuous. This gives a `BottomChart` with monotone coordinate on `L`; every
bounded path lies in one of them.
-/

noncomputable section

open Set Topology Ordinal Order

namespace RealContinuity

instance : NoMaxOrder W := ⟨fun a => W.exists_gt a⟩

/-- Initial segments of `W` are countable. -/
theorem W.countable_Iio (b : W) : (Iio b).Countable := by
  have hb : ((ToType.mk.symm b : Iio (ω₁ : Ordinal.{0})) : Ordinal) < ω₁ :=
    (ToType.mk.symm b).2
  have hc := Cardinal.countable_Iio_of_lt_omega_one hb
  have hinj : Function.Injective (fun a : W => ((ToType.mk.symm a : Iio (ω₁ : Ordinal.{0})) :
      Ordinal)) := fun a a' h => ToType.mk.symm.injective (Subtype.ext h)
  refine (hc.preimage hinj).mono ?_
  intro a ha
  simp only [mem_preimage, mem_Iio]
  have : ToType.mk.symm a < ToType.mk.symm b := ToType.mk.symm.lt_iff_lt.mpr ha
  exact this

namespace Chart

variable (b : W)

/-- An injection of the predecessors of `b` into `ℕ`. -/
def idx : Iio b → ℕ := Classical.choose (W.countable_Iio b).exists_injective_nat'

theorem idx_injective : Function.Injective (idx b) :=
  Classical.choose_spec (W.countable_Iio b).exists_injective_nat'

/-- The weight of the unit interval indexed by `a`: positive below `b`, zero
from `b` on. -/
def w (a : W) : ℝ := if h : a < b then (1 / 2 : ℝ) ^ idx b ⟨a, h⟩ else 0

theorem w_nonneg (a : W) : 0 ≤ w b a := by
  unfold w; split_ifs <;> positivity

theorem w_pos {a : W} (h : a < b) : 0 < w b a := by
  simp [w, h]

theorem w_of_le {a : W} (h : b ≤ a) : w b a = 0 := by
  simp [w, not_lt.mpr h]

theorem summable_w : Summable (w b) := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := summable_geometric_two
  have hsub : Summable (fun x : Iio b => (1 / 2 : ℝ) ^ idx b x) :=
    hg.comp_injective (idx_injective b)
  have hind : Summable ((Iio b).indicator (fun a => if h : a < b then
      (1 / 2 : ℝ) ^ idx b ⟨a, h⟩ else 0)) := by
    rw [← summable_subtype_iff_indicator]
    refine hsub.congr fun x => ?_
    have hx : (x : W) < b := x.2
    simp only [Function.comp_apply, hx, dite_true]
  refine hind.congr fun a => ?_
  by_cases h : a < b
  · simp [w, h]
  · simp [w, h]

/-- `F a = Σ_{c < a} w c`. -/
def F (a : W) : ℝ := ∑' c, (Iio a).indicator (w b) c

theorem summable_ind (a : W) : Summable ((Iio a).indicator (w b)) :=
  (summable_w b).indicator _

theorem F_nonneg (a : W) : 0 ≤ F b a :=
  tsum_nonneg fun c => indicator_nonneg (fun c _ => w_nonneg b c) c

theorem F_mono : Monotone (F b) := by
  intro a a' h
  refine (summable_ind b a).tsum_le_tsum (fun c => ?_) (summable_ind b a')
  exact indicator_le_indicator_of_subset (Iio_subset_Iio h) (fun c => w_nonneg b c) c

/-- `F (succ a) = F a + w a`. -/
theorem F_succ (a : W) : F b (succ a) = F b a + w b a := by
  classical
  unfold F
  rw [Iio_succ]
  have hs : Summable (Function.update ((Iic a).indicator (w b)) a 0) := by
    refine ((summable_w b).indicator (Iic a)).update a 0
  rw [Summable.tsum_eq_add_tsum_ite' a hs, add_comm (∑' c, (Iio a).indicator (w b) c)]
  congr 1
  · simp
  · refine tsum_congr fun c => ?_
    by_cases hca : c = a
    · subst hca; simp
    · rcases lt_or_gt_of_ne hca with h | h
      · simp [hca, h, h.le]
      · simp [hca, not_le.mpr h, not_lt.mpr h.le]

/-- `F` is constant from `b` on: all the weight lies below `b`. -/
theorem F_of_le {a : W} (h : b ≤ a) : F b a = F b b := by
  unfold F
  refine tsum_congr fun c => ?_
  by_cases hc : c < b
  · rw [indicator_of_mem (show c ∈ Iio a from hc.trans_le h),
      indicator_of_mem (show c ∈ Iio b from hc)]
  · rw [indicator_of_notMem (show c ∉ Iio b from hc)]
    by_cases hca : c < a
    · rw [indicator_of_mem (show c ∈ Iio a from hca), w_of_le b (not_lt.mp hc)]
    · rw [indicator_of_notMem (show c ∉ Iio a from hca)]

/-- The total length `S_b`. -/
def S : ℝ := F b b

theorem S_nonneg : 0 ≤ S b := F_nonneg b b

theorem F_le_S (a : W) : F b a ≤ S b := by
  rcases le_total a b with h | h
  · exact F_mono b h
  · exact (F_of_le b h).le

/-- At a successor-prelimit `a`, `F a` is bounded by any bound of its earlier values. -/
theorem F_le_of_prelimit {a : W} (ha : IsSuccPrelimit a) {s : ℝ} (hs0 : 0 ≤ s)
    (h : ∀ c < a, F b c ≤ s) : F b a ≤ s := by
  classical
  refine (summable_ind b a).tsum_le_of_sum_le fun t => ?_
  by_cases hne : (t.filter (· < a)).Nonempty
  · set m := (t.filter (· < a)).max' hne with hm_def
    have hm : m < a := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    have hsm : succ m < a := ha.succ_lt hm
    calc ∑ i ∈ t, (Iio a).indicator (w b) i
        ≤ ∑ i ∈ t, (Iio (succ m)).indicator (w b) i := by
          refine Finset.sum_le_sum fun i hi => ?_
          by_cases hia : i < a
          · have him : i ≤ m := Finset.le_max' _ i (Finset.mem_filter.mpr ⟨hi, hia⟩)
            rw [indicator_of_mem (show i ∈ Iio a from hia),
              indicator_of_mem (show i ∈ Iio (succ m) from lt_succ_of_le him)]
          · rw [indicator_of_notMem (show i ∉ Iio a from hia)]
            exact indicator_nonneg (fun c _ => w_nonneg b c) i
      _ ≤ ∑' i, (Iio (succ m)).indicator (w b) i :=
          (summable_ind b (succ m)).sum_le_tsum t
            (fun i _ => indicator_nonneg (fun c _ => w_nonneg b c) i)
      _ ≤ s := h _ hsm
  · have hz : ∑ i ∈ t, (Iio a).indicator (w b) i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : ¬ i < a := fun hia => hne ⟨i, Finset.mem_filter.mpr ⟨hi, hia⟩⟩
      exact indicator_of_notMem (show i ∉ Iio a from this) _
    rw [hz]; exact hs0

/-! ### The coordinate -/

/-- The chart coordinate of a finite point. -/
def φ₀ (x : L₀) : ℝ := F b (ofLex x).1 + ((ofLex x).2 : ℝ) * w b (ofLex x).1

theorem F_le_φ₀ (x : L₀) : F b (ofLex x).1 ≤ φ₀ b x := by
  unfold φ₀
  have := w_nonneg b (ofLex x).1
  have := (ofLex x).2.2.1
  nlinarith

theorem φ₀_le_F_succ (x : L₀) : φ₀ b x ≤ F b (succ (ofLex x).1) := by
  rw [F_succ]; unfold φ₀
  have := w_nonneg b (ofLex x).1
  have := (ofLex x).2.2.2.le
  nlinarith

theorem φ₀_lt_F_succ {x : L₀} (hx : (ofLex x).1 < b) : φ₀ b x < F b (succ (ofLex x).1) := by
  rw [F_succ]; unfold φ₀
  have := w_pos b hx
  have := (ofLex x).2.2.2
  nlinarith

theorem φ₀_nonneg (x : L₀) : 0 ≤ φ₀ b x := (F_nonneg b _).trans (F_le_φ₀ b x)

theorem φ₀_le_S (x : L₀) : φ₀ b x ≤ S b := (φ₀_le_F_succ b x).trans (F_le_S b _)

theorem φ₀_mono : Monotone (φ₀ b) := by
  intro x y hxy
  rcases Prod.Lex.le_iff.mp hxy with h | ⟨h1, h2⟩
  · calc φ₀ b x ≤ F b (succ (ofLex x).1) := φ₀_le_F_succ b x
      _ ≤ F b (ofLex y).1 := F_mono b (succ_le_of_lt h)
      _ ≤ φ₀ b y := F_le_φ₀ b y
  · unfold φ₀
    rw [h1]
    have := w_nonneg b (ofLex y).1
    have h2' : ((ofLex x).2 : ℝ) ≤ (ofLex y).2 := h2
    nlinarith

theorem φ₀_strictMonoOn : StrictMonoOn (φ₀ b) {x | (ofLex x).1 < b} := by
  intro x hx y _ hxy
  rcases Prod.Lex.lt_iff.mp hxy with h | ⟨h1, h2⟩
  · calc φ₀ b x < F b (succ (ofLex x).1) := φ₀_lt_F_succ b hx
      _ ≤ F b (ofLex y).1 := F_mono b (succ_le_of_lt h)
      _ ≤ φ₀ b y := F_le_φ₀ b y
  · unfold φ₀
    rw [h1]
    have hw := w_pos b (show (ofLex y).1 < b from h1 ▸ hx)
    have h2' : ((ofLex x).2 : ℝ) < (ofLex y).2 := h2
    nlinarith

/-- Every value in `[0, S)` is attained below `(b, 0)`. -/
theorem exists_φ₀_eq {s : ℝ} (hs0 : 0 ≤ s) (hsS : s < S b) :
    ∃ x : L₀, (ofLex x).1 < b ∧ φ₀ b x = s := by
  obtain ⟨a, ha, hmin⟩ := (wellFounded_lt (α := W)).has_min {a | s < F b a}
    ⟨b, (show s < F b b from hsS)⟩
  have hle : ∀ c < a, F b c ≤ s := fun c hc => not_lt.mp fun h => hmin c h hc
  have hnot : ¬ IsSuccPrelimit a := fun hl => absurd (F_le_of_prelimit b hl hs0 hle)
    (not_le.mpr ha)
  obtain ⟨a₀, -, rfl⟩ := not_isSuccPrelimit_iff_succ_eq.mp hnot
  have ha₀ : a₀ < succ a₀ := lt_succ a₀
  have hFa₀ : F b a₀ ≤ s := hle a₀ ha₀
  have hab : succ a₀ ≤ b := by
    by_contra hcon
    exact hmin b (show s < F b b from hsS) (not_le.mp hcon)
  have hlt : a₀ < b := lt_of_lt_of_le ha₀ hab
  have hw := w_pos b hlt
  have hs' : s < F b a₀ + w b a₀ := by rw [← F_succ]; exact ha
  set t : ℝ := (s - F b a₀) / w b a₀ with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hw.le
  have ht1 : t < 1 := by rw [ht, div_lt_one hw]; linarith
  refine ⟨toLex (a₀, ⟨t, ht0, ht1⟩), hlt, ?_⟩
  simp only [φ₀, ofLex_toLex]
  rw [ht]; field_simp; ring

/-- The chart coordinate on `L`, constant `S` at `∞`. -/
def Φfun (x : L) : ℝ := WithTop.recTopCoe (S b) (φ₀ b) x

@[simp] theorem Φfun_coe (x : L₀) : Φfun b (x : L) = φ₀ b x := rfl

@[simp] theorem Φfun_top : Φfun b ⊤ = S b := rfl

theorem Φfun_mono : Monotone (Φfun b) := by
  intro x y hxy
  induction x using WithTop.recTopCoe with
  | top =>
    have : y = ⊤ := top_le_iff.mp hxy
    rw [this]
  | coe x =>
    induction y using WithTop.recTopCoe with
    | top => exact φ₀_le_S b x
    | coe y => exact φ₀_mono b (WithTop.coe_le_coe.mp hxy)

theorem Φfun_nonneg (x : L) : 0 ≤ Φfun b x := by
  induction x using WithTop.recTopCoe with
  | top => exact S_nonneg b
  | coe x => exact φ₀_nonneg b x

theorem Φfun_le_S (x : L) : Φfun b x ≤ S b := by
  induction x using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe x => exact φ₀_le_S b x

theorem Φfun_ordPt : Φfun b (ordPt b) = S b := by
  simp [ordPt, φ₀, S]

/-- Below `(b, 0)` the coordinate stays below `S`. -/
theorem fst_lt_of_lt_ordPt {x : L₀} (hx : (x : L) < ordPt b) : (ofLex x).1 < b := by
  have hx' : x < toLex (b, (⟨0, le_rfl, zero_lt_one⟩ : Ico (0 : ℝ) 1)) :=
    WithTop.coe_lt_coe.mp hx
  rcases Prod.Lex.lt_iff.mp hx' with h | ⟨h1, h2⟩
  · simpa using h
  · exact absurd h2 (not_lt.mpr (ofLex x).2.2.1)

theorem Φfun_lt_S_of_lt_ordPt {x : L} (hx : x < ordPt b) : Φfun b x < S b := by
  induction x using WithTop.recTopCoe with
  | top => exact absurd hx (not_lt.mpr le_top)
  | coe x => exact (φ₀_lt_F_succ b (fst_lt_of_lt_ordPt b hx)).trans_le (F_le_S b _)

theorem lt_ordPt_of_Φfun_lt_S {x : L} (hx : Φfun b x < S b) : x < ordPt b := by
  by_contra h
  have := Φfun_mono b (not_lt.mp h)
  rw [Φfun_ordPt] at this
  linarith

/-! ### The chart -/

/-- The coordinate on the initial segment `[0, (b,0))`, valued in `[0, S)`. -/
def toIco (x : Iio (ordPt b)) : Ico (0 : ℝ) (S b) :=
  ⟨Φfun b x, Φfun_nonneg b x, Φfun_lt_S_of_lt_ordPt b x.2⟩

theorem toIco_strictMono : StrictMono (toIco b) := by
  intro x y hxy
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  change Φfun b x < Φfun b y
  induction x using WithTop.recTopCoe with
  | top => exact absurd (show (⊤ : L) < ordPt b from hx) (not_lt.mpr le_top)
  | coe x =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd (show (⊤ : L) < ordPt b from hy) (not_lt.mpr le_top)
    | coe y =>
      exact φ₀_strictMonoOn b (fst_lt_of_lt_ordPt b hx) (fst_lt_of_lt_ordPt b hy)
        (WithTop.coe_lt_coe.mp hxy)

theorem toIco_surjective : Function.Surjective (toIco b) := by
  rintro ⟨s, hs0, hsS⟩
  obtain ⟨x, hx, rfl⟩ := exists_φ₀_eq b hs0 hsS
  exact ⟨⟨(x : L), coe_lt_ordPt hx⟩, rfl⟩

/-- The initial segment `[0, (b,0))` is order isomorphic to `[0, S)`. -/
def segIso : Iio (ordPt b) ≃o Ico (0 : ℝ) (S b) :=
  StrictMono.orderIsoOfSurjective (toIco b) (toIco_strictMono b) (toIco_surjective b)

/-- ... hence homeomorphic. -/
def segHomeo : Iio (ordPt b) ≃ₜ Ico (0 : ℝ) (S b) := (segIso b).toHomeomorph

theorem continuous_Φfun : Continuous (Φfun b) := by
  let g : L → Icc (0 : ℝ) (S b) := fun x => ⟨Φfun b x, Φfun_nonneg b x, Φfun_le_S b x⟩
  have hg : Monotone g := fun x y h => Φfun_mono b h
  have hgs : Function.Surjective g := by
    rintro ⟨s, hs0, hsS⟩
    rcases eq_or_lt_of_le hsS with h | h
    · exact ⟨⊤, Subtype.ext (by simp [g, h])⟩
    · obtain ⟨x, hx, hxs⟩ := exists_φ₀_eq b hs0 h
      exact ⟨(x : L), Subtype.ext (by simp [g, hxs])⟩
  exact continuous_subtype_val.comp (hg.continuous_of_surjective hgs)

/-- **The long-ray chart below `(b, 0)`.** -/
def chart : BottomChart L where
  Φ := ⟨Φfun b, continuous_Φfun b⟩
  β := S b
  ψ := ⟨fun s => ((segHomeo b).symm s : L),
    continuous_subtype_val.comp (segHomeo b).symm.continuous⟩
  nonneg := Φfun_nonneg b
  Φ_ψ := by
    intro s
    have h := (segIso b).apply_symm_apply s
    exact congrArg Subtype.val h
  ψ_Φ := by
    intro x hx
    have hx' : x < ordPt b := lt_ordPt_of_Φfun_lt_S b hx
    have h : (segIso b) ⟨x, hx'⟩ = ⟨Φfun b x, Φfun_nonneg b x, hx⟩ := rfl
    change (((segIso b).symm ⟨Φfun b x, Φfun_nonneg b x, hx⟩ : Iio (ordPt b)) : L) = x
    rw [← h, OrderIso.symm_apply_apply]

theorem chart_mono : Monotone (chart b).Φ := Φfun_mono b

theorem chart_J : (chart b).J = Iio (ordPt b) := by
  ext x
  exact ⟨lt_ordPt_of_Φfun_lt_S b, Φfun_lt_S_of_lt_ordPt b⟩

end Chart

/-- Every path bounded below an ordinal point has an admissible chart ball. -/
theorem exists_admissible {γ : C(unitInterval, L)} {b : W} (hγ : ∀ t, γ t < ordPt b) :
    ∃ ε, (Chart.chart b).Admissible γ ε := by
  obtain ⟨t, ht⟩ := OrderHomotopy.exists_eq_pathMax ((Chart.chart b).coord γ)
  set M := OrderHomotopy.pathMax ((Chart.chart b).coord γ) with hMdef
  have hM : M < Chart.S b := by
    rw [← ht]
    exact Chart.Φfun_lt_S_of_lt_ordPt b (hγ t)
  refine ⟨(Chart.S b - M) / 2, ⟨by linarith, ?_⟩⟩
  change M + (Chart.S b - M) / 2 < Chart.S b
  linarith

end RealContinuity
