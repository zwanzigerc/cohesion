import PointlessEnd.Glued
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The minimal chart category

The charts are the point, the real line, and the pointless-end locales `L_e` for
`e ≠ ⊥`. Morphisms are all locale maps: a morphism `U ⟶ V` is a frame homomorphism
`O(V) → O(U)`. There are no locale products.

* **Points.** A point of a chart is a map `pt ⟶ U`. The point chart is terminal. Every
  chart has a point; every nonzero open of a chart contains one. The points of `ℝ` are the
  real numbers and the points of `L_e` are its collar points.
* **Open embeddings.** `IsOpenEmb f a`: `f^*` restricts to an isomorphism `↓a ≅ O(T)`.
  Open embeddings compose, and a map `h` with `h^*(a) = ⊤` factors uniquely through an open
  embedding with image `a` (`IsOpenEmb.lift`).
* **Basic open embeddings.** Intervals `ℝ → ℝ`, collar intervals `ℝ → L_e`, and rescaled
  initial pieces `L_d → L_e` (`d ≤ e`, onto `((0, ε), d)`).
* **Chart basis** (`basis`): every open of a chart is the join of the images of the basic
  open embeddings it contains.
* **Connectedness**: complemented opens of a chart are trivial.
* **Paths**: any two points of a chart are joined by a map `ℝ ⟶ U` (`exists_path`).
-/

noncomputable section

open Set TopologicalSpace CategoryTheory

namespace PointlessEnd

/-! ### Interval homeomorphisms -/

/-- An open embedding `ℝ → ℝ` onto `(a, b)`. -/
def ivlMap (a b : ℝ) (x : ℝ) : ℝ := (a + b) / 2 + (b - a) / 2 * (orderIsoIooNegOneOne ℝ x : ℝ)

theorem ivlMap_mem {a b : ℝ} (hab : a < b) (x : ℝ) : ivlMap a b x ∈ Ioo a b := by
  have h := (orderIsoIooNegOneOne ℝ x).2
  simp only [mem_Ioo] at h
  simp only [ivlMap, mem_Ioo]
  constructor <;> nlinarith [h.1, h.2]

theorem range_ivlMap {a b : ℝ} (hab : a < b) : range (ivlMap a b) = Ioo a b := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ivlMap_mem hab x
  · intro hy
    have hba : 0 < b - a := sub_pos.mpr hab
    set z := (2 * y - (a + b)) / (b - a) with hz
    have hz1 : z ∈ Ioo (-1 : ℝ) 1 := by
      rw [hz, mem_Ioo, lt_div_iff₀ hba, div_lt_iff₀ hba]
      constructor <;> linarith [hy.1, hy.2]
    obtain ⟨x, hx⟩ := (orderIsoIooNegOneOne ℝ).surjective ⟨z, hz1⟩
    refine ⟨x, ?_⟩
    simp only [ivlMap, hx, hz]
    field_simp
    ring

theorem isOpenEmbedding_ivlMap {a b : ℝ} (hab : a < b) : Topology.IsOpenEmbedding (ivlMap a b) := by
  have h1 : Topology.IsOpenEmbedding (fun x : ℝ => ((orderIsoIooNegOneOne ℝ x : Ioo (-1:ℝ) 1) : ℝ)) :=
    (isOpen_Ioo.isOpenEmbedding_subtypeVal).comp
      (orderIsoIooNegOneOne ℝ).toHomeomorph.isOpenEmbedding
  have hne : (b - a) / 2 ≠ 0 := by
    have : 0 < b - a := sub_pos.mpr hab
    positivity
  have h2 : Topology.IsOpenEmbedding (fun t : ℝ => (a + b) / 2 + (b - a) / 2 * t) :=
    ((Homeomorph.mulLeft₀ ((b - a) / 2) hne).trans (Homeomorph.addLeft ((a + b) / 2))).isOpenEmbedding
  exact h2.comp h1

theorem continuous_ivlMap {a b : ℝ} (hab : a < b) : Continuous (ivlMap a b) :=
  (isOpenEmbedding_ivlMap hab).continuous

/-! ### Locale maps from continuous maps -/

/-- The locale map `ℝ → L_e` through the collar, from a continuous map into `(0, 1)`. -/
def collarHom (e : P) (γ : C(ℝ, ℝ)) (hγ : ∀ x, γ x ∈ Ioo (0 : ℝ) 1) : FrameHom (G e) (Opens ℝ) where
  toFun y := Opens.comap γ y.V
  map_inf' _ _ := map_inf (Opens.comap γ) _ _
  map_top' := Opens.ext (eq_univ_of_forall fun x => hγ x)
  map_sSup' S := by
    change Opens.comap γ (⨆ x ∈ S, x.V) = _
    rw [map_iSup₂, sSup_image]

@[simp] theorem collarHom_apply (e : P) (γ : C(ℝ, ℝ)) (hγ) (y : G e) :
    collarHom e γ hγ y = Opens.comap γ y.V := rfl

/-! ### Charts -/

/-- **The charts**: the point, the real line, and the pointless-end locales. -/
inductive Chart
  | pt
  | real
  | endc (e : P) (he : e ≠ ⊥)

namespace Chart

/-- The frame of opens of a chart. -/
@[reducible] def O : Chart → Type
  | pt => Prop
  | real => Opens ℝ
  | endc e _ => G e

instance instFrame : (U : Chart) → Order.Frame (O U)
  | pt => inferInstanceAs (Order.Frame Prop)
  | real => inferInstanceAs (Order.Frame (Opens ℝ))
  | endc e _ => inferInstanceAs (Order.Frame (G e))

/-- **The chart category**: all locale maps. -/
instance : SmallCategory Chart where
  Hom U V := FrameHom (O V) (O U)
  id _ := FrameHom.id _
  comp f g := FrameHom.comp f g
  id_comp f := FrameHom.id_comp f
  comp_id f := FrameHom.comp_id f
  assoc f g h := FrameHom.comp_assoc f g h

instance instFunLike (U V : Chart) : FunLike (U ⟶ V) (O V) (O U) :=
  inferInstanceAs (FunLike (FrameHom (O V) (O U)) (O V) (O U))

instance instFHC (U V : Chart) : FrameHomClass (U ⟶ V) (O V) (O U) :=
  inferInstanceAs (FrameHomClass (FrameHom (O V) (O U)) (O V) (O U))

/-! The frame-homomorphism class at concrete charts. `O` is reducible, so instance search
sees the concrete frames `Prop`, `Opens ℝ` and `G e`; these instances restate `instFHC`
with those keys. -/

instance (U : Chart) : FrameHomClass (U ⟶ pt) Prop (O U) := instFHC U pt
instance (U : Chart) : FrameHomClass (U ⟶ real) (Opens ℝ) (O U) := instFHC U real
instance (U : Chart) (e : P) (he : e ≠ ⊥) : FrameHomClass (U ⟶ endc e he) (G e) (O U) :=
  instFHC U _
instance (V : Chart) : FrameHomClass (pt ⟶ V) (O V) Prop := instFHC pt V
instance (V : Chart) : FrameHomClass (real ⟶ V) (O V) (Opens ℝ) := instFHC real V
instance (V : Chart) (e : P) (he : e ≠ ⊥) : FrameHomClass (endc e he ⟶ V) (O V) (G e) :=
  instFHC _ V
instance : FrameHomClass (pt ⟶ pt) Prop Prop := instFHC pt pt
instance : FrameHomClass (pt ⟶ real) (Opens ℝ) Prop := instFHC pt real
instance (e : P) (he : e ≠ ⊥) : FrameHomClass (pt ⟶ endc e he) (G e) Prop := instFHC pt _
instance : FrameHomClass (real ⟶ pt) Prop (Opens ℝ) := instFHC real pt
instance : FrameHomClass (real ⟶ real) (Opens ℝ) (Opens ℝ) := instFHC real real
instance (e : P) (he : e ≠ ⊥) : FrameHomClass (real ⟶ endc e he) (G e) (Opens ℝ) :=
  instFHC real _
instance (e : P) (he : e ≠ ⊥) : FrameHomClass (endc e he ⟶ pt) Prop (G e) := instFHC _ pt
instance (e : P) (he : e ≠ ⊥) : FrameHomClass (endc e he ⟶ real) (Opens ℝ) (G e) :=
  instFHC _ real
instance (e d : P) (he : e ≠ ⊥) (hd : d ≠ ⊥) : FrameHomClass (endc d hd ⟶ endc e he) (G e) (G d) :=
  instFHC _ _

/-- A frame homomorphism as a chart map. -/
def ofFrameHom {U V : Chart} (h : FrameHom (O V) (O U)) : U ⟶ V := h

/-- A chart map as a frame homomorphism. -/
def toFrameHom {U V : Chart} (f : U ⟶ V) : FrameHom (O V) (O U) := f

@[simp] theorem ofFrameHom_apply {U V : Chart} (h : FrameHom (O V) (O U)) (a : O V) :
    ofFrameHom h a = h a := rfl

@[simp] theorem toFrameHom_apply {U V : Chart} (f : U ⟶ V) (a : O V) :
    toFrameHom f a = f a := rfl

@[simp] theorem comp_apply {U V W : Chart} (f : U ⟶ V) (g : V ⟶ W) (a : O W) :
    (f ≫ g) a = f (g a) := rfl

@[simp] theorem id_apply {U : Chart} (a : O U) : (𝟙 U : U ⟶ U) a = a := rfl

@[ext] theorem hom_ext {U V : Chart} {f g : U ⟶ V} (h : ∀ a, f a = g a) : f = g :=
  FrameHom.ext h

theorem hom_mono {U V : Chart} (f : U ⟶ V) {a b : O V} (h : a ≤ b) : f a ≤ f b :=
  OrderHomClass.mono f h

/-! ### The point -/

/-- The unique frame homomorphism out of `Prop`. -/
def propHom (A : Type*) [Order.Frame A] : FrameHom Prop A where
  toFun p := ⨆ (_ : p), ⊤
  map_inf' p q := by
    by_cases hp : p <;> by_cases hq : q
    · rw [iSup_pos hp, iSup_pos hq, iSup_pos (show p ⊓ q from ⟨hp, hq⟩), inf_top_eq]
    · rw [iSup_pos hp, iSup_neg hq, iSup_neg (show ¬ (p ⊓ q) from fun h => hq h.2), inf_bot_eq]
    · rw [iSup_neg hp, iSup_neg (show ¬ (p ⊓ q) from fun h => hp h.1), bot_inf_eq]
    · rw [iSup_neg hp, iSup_neg (show ¬ (p ⊓ q) from fun h => hp h.1), bot_inf_eq]
  map_top' := iSup_pos trivial
  map_sSup' S := by
    rw [sSup_image]
    by_cases h : ∃ p ∈ S, p
    · obtain ⟨p, hp, hpp⟩ := h
      rw [iSup_pos (show sSup S from ⟨p, hp, hpp⟩)]
      have h1 : (⨆ (_ : p), (⊤ : A)) = ⊤ := iSup_pos hpp
      exact (top_unique (le_iSup₂_of_le (f := fun p (_ : p ∈ S) => ⨆ (_ : p), (⊤ : A)) p hp h1.ge)).symm
    · rw [iSup_neg (show ¬ sSup S from fun ⟨p, hp, hpp⟩ => h ⟨p, hp, hpp⟩)]
      refine (le_antisymm (iSup₂_le fun p hp => ?_) bot_le).symm
      exact (iSup_neg (fun hpp => h ⟨p, hp, hpp⟩)).le

theorem propHom_unique {A : Type*} [Order.Frame A] (f : FrameHom Prop A) : f = propHom A := by
  ext p
  by_cases hp : p
  · rw [eq_true hp]
    change f ⊤ = propHom A ⊤
    rw [map_top, map_top]
  · rw [eq_false hp]
    change f ⊥ = propHom A ⊥
    rw [map_bot, map_bot]

/-- The unique map to the point. -/
def toPt (U : Chart) : U ⟶ pt := propHom (O U)

theorem toPt_eq {U : Chart} (f : U ⟶ pt) : f = toPt U := propHom_unique f

theorem toPt_pt : toPt pt = 𝟙 pt := (toPt_eq _).symm

/-- The point chart is terminal. -/
def isTerminalPt : Limits.IsTerminal pt :=
  Limits.IsTerminal.ofUniqueHom (fun U => toPt U) (fun _ f => toPt_eq f)

/-- The point of `ℝ` at `x`. -/
def ptAt (x : ℝ) : pt ⟶ real := ptHom x

@[simp] theorem ptAt_apply (x : ℝ) (W : Opens ℝ) : (ptAt x : pt ⟶ real) W ↔ x ∈ W := Iff.rfl

theorem real_point (p : pt ⟶ real) : ∃ x, p = ptAt x := ptHom_surjective p

/-- The collar point of `L_e` at `x`. -/
def ptEnd {e : P} (he : e ≠ ⊥) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : pt ⟶ endc e he :=
  collarPt e x hx

theorem end_point {e : P} {he : e ≠ ⊥} (p : pt ⟶ endc e he) :
    ∃ (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1), p = ptEnd he x hx :=
  point_eq_collarPt p

/-- **Every nonzero open of a chart contains a point.** -/
theorem exists_point (U : Chart) {b : O U} (hb : b ≠ ⊥) : ∃ p : pt ⟶ U, p b := by
  cases U with
  | pt =>
    refine ⟨𝟙 pt, ?_⟩
    by_contra h
    exact hb (eq_false h)
  | real =>
    have : ((b : Opens ℝ) : Set ℝ).Nonempty := by
      by_contra h
      exact hb (Opens.ext (not_nonempty_iff_eq_empty.mp h))
    obtain ⟨x, hx⟩ := this
    exact ⟨ptAt x, hx⟩
  | endc e he => exact exists_point_of_ne_bot hb

theorem bot_ne_top (U : Chart) : (⊥ : O U) ≠ ⊤ := by
  cases U with
  | pt =>
    intro h
    have : (⊤ : Prop) := trivial
    rw [← h] at this
    exact this
  | real =>
    intro h
    have : (0 : ℝ) ∈ (⊤ : Opens ℝ) := trivial
    rw [← h] at this
    exact this
  | endc e he => exact G.bot_ne_top

theorem nonempty_point (U : Chart) : Nonempty (pt ⟶ U) :=
  let ⟨p, _⟩ := exists_point U (bot_ne_top U).symm
  ⟨p⟩

/-- **Charts are connected**: complemented opens are trivial. -/
theorem eq_bot_or_eq_bot (U : Chart) {y z : O U} (hinf : y ⊓ z = ⊥) (hsup : y ⊔ z = ⊤) :
    y = ⊥ ∨ z = ⊥ := by
  cases U with
  | pt =>
    by_cases hy : (y : Prop)
    · right
      apply eq_false
      intro hz
      have : (y ⊓ z : Prop) := ⟨hy, hz⟩
      rw [hinf] at this
      exact this
    · left
      exact eq_false hy
  | real =>
    have hV1 : ((y : Opens ℝ) : Set ℝ) ∩ (z : Opens ℝ) = ∅ := congrArg (fun w : Opens ℝ => (w : Set ℝ)) hinf
    have hV2 : ((y : Opens ℝ) : Set ℝ) ∪ (z : Opens ℝ) = univ := congrArg (fun w : Opens ℝ => (w : Set ℝ)) hsup
    by_contra hne
    rw [not_or] at hne
    obtain ⟨a, ha⟩ : ((y : Opens ℝ) : Set ℝ).Nonempty := by
      by_contra h
      exact hne.1 (Opens.ext (not_nonempty_iff_eq_empty.mp h))
    obtain ⟨b, hb⟩ : ((z : Opens ℝ) : Set ℝ).Nonempty := by
      by_contra h
      exact hne.2 (Opens.ext (not_nonempty_iff_eq_empty.mp h))
    obtain ⟨c, -, hc1, hc2⟩ := isPreconnected_univ (α := ℝ) _ _ (y : Opens ℝ).isOpen
      (z : Opens ℝ).isOpen hV2.symm.le ⟨a, trivial, ha⟩ ⟨b, trivial, hb⟩
    have : c ∈ ((y : Opens ℝ) : Set ℝ) ∩ (z : Opens ℝ) := ⟨hc1, hc2⟩
    rw [hV1] at this
    exact this
  | endc e he => exact G.eq_bot_or_eq_bot hinf hsup

/-! ### Open embeddings -/

/-- `f : T ⟶ U` is an **open embedding with image `a`**: `f^*` restricts to an
isomorphism `↓a ≅ O(T)`, with inverse `inv`. -/
def IsOpenEmb {T U : Chart} (f : T ⟶ U) (a : O U) : Prop :=
  ∃ inv : O T → O U, (∀ y, inv y ≤ a) ∧ (∀ y, f (inv y) = y) ∧ (∀ b, inv (f b) = b ⊓ a)

namespace IsOpenEmb

variable {T U W : Chart} {f : T ⟶ U} {a : O U}

/-- The inverse `f_!`. -/
def inv (hf : IsOpenEmb f a) : O T → O U := Classical.choose hf

theorem inv_le (hf : IsOpenEmb f a) (y : O T) : hf.inv y ≤ a := (Classical.choose_spec hf).1 y

theorem map_inv (hf : IsOpenEmb f a) (y : O T) : f (hf.inv y) = y := (Classical.choose_spec hf).2.1 y

theorem inv_map (hf : IsOpenEmb f a) (b : O U) : hf.inv (f b) = b ⊓ a :=
  (Classical.choose_spec hf).2.2 b

theorem map_img (hf : IsOpenEmb f a) : f a = ⊤ :=
  top_unique ((hf.map_inv ⊤).symm.le.trans (hom_mono f (hf.inv_le ⊤)))

theorem inv_top (hf : IsOpenEmb f a) : hf.inv ⊤ = a := by
  rw [← hf.map_img, hf.inv_map, inf_idem]

theorem inv_inf (hf : IsOpenEmb f a) (y y' : O T) : hf.inv (y ⊓ y') = hf.inv y ⊓ hf.inv y' := by
  have h := hf.inv_map (hf.inv y ⊓ hf.inv y')
  rw [map_inf, hf.map_inv, hf.map_inv] at h
  rw [h, inf_eq_left.mpr (inf_le_left.trans (hf.inv_le y))]

theorem inv_mono (hf : IsOpenEmb f a) {y y' : O T} (h : y ≤ y') : hf.inv y ≤ hf.inv y' := by
  rw [← inf_eq_left.mpr h, hf.inv_inf]
  exact inf_le_right

theorem inv_sSup (hf : IsOpenEmb f a) (S : Set (O T)) : hf.inv (sSup S) = ⨆ y ∈ S, hf.inv y := by
  have h := hf.inv_map (⨆ y ∈ S, hf.inv y)
  rw [map_iSup₂] at h
  simp only [hf.map_inv] at h
  rw [← sSup_eq_iSup] at h
  rw [h, inf_eq_left.mpr (iSup₂_le fun y _ => hf.inv_le y)]

theorem inv_iSup (hf : IsOpenEmb f a) {ι : Sort*} (g : ι → O T) :
    hf.inv (⨆ i, g i) = ⨆ i, hf.inv (g i) := by
  rw [iSup, hf.inv_sSup, iSup_range]

theorem inv_bot (hf : IsOpenEmb f a) : hf.inv ⊥ = ⊥ := by
  rw [← sSup_empty, hf.inv_sSup]
  simp

theorem inv_injective (hf : IsOpenEmb f a) : Function.Injective hf.inv := fun y y' h => by
  rw [← hf.map_inv y, ← hf.map_inv y', h]

theorem img_ne_bot (hf : IsOpenEmb f a) : a ≠ ⊥ := by
  intro h
  have := hf.map_img
  rw [h, map_bot] at this
  exact bot_ne_top T this

/-- `b ⊓ a = f_!(f^* b)`. -/
theorem inf_img (hf : IsOpenEmb f a) (b : O U) : b ⊓ a = hf.inv (f b) := (hf.inv_map b).symm

/-- **Factorization through an open embedding.** -/
def lift (hf : IsOpenEmb f a) (h : W ⟶ U) (hh : h a = ⊤) : W ⟶ T where
  toFun y := h (hf.inv y)
  map_inf' y y' := by rw [hf.inv_inf, map_inf]
  map_top' := by rw [hf.inv_top, hh]
  map_sSup' S := by
    rw [hf.inv_sSup, map_iSup₂, sSup_image]

@[simp] theorem lift_apply (hf : IsOpenEmb f a) (h : W ⟶ U) (hh : h a = ⊤) (y : O T) :
    hf.lift h hh y = h (hf.inv y) := rfl

@[simp] theorem lift_comp (hf : IsOpenEmb f a) (h : W ⟶ U) (hh : h a = ⊤) : hf.lift h hh ≫ f = h := by
  ext b
  change h (hf.inv (f b)) = h b
  rw [hf.inv_map, map_inf, hh, inf_top_eq]

theorem eq_lift (hf : IsOpenEmb f a) {h : W ⟶ U} (hh : h a = ⊤) {k : W ⟶ T} (hk : k ≫ f = h) :
    k = hf.lift h hh := by
  ext y
  change k y = h (hf.inv y)
  rw [← hk, comp_apply, hf.map_inv]

/-- Maps landing in the image factor through the open embedding. -/
theorem comp_eq_iff (hf : IsOpenEmb f a) {k k' : W ⟶ T} : k ≫ f = k' ≫ f ↔ k = k' := by
  constructor
  · intro h
    ext y
    have := congrArg (fun m : W ⟶ U => m (hf.inv y)) h
    simpa only [comp_apply, hf.map_inv] using this
  · rintro rfl
    rfl

theorem comp_map_img {k : W ⟶ T} (hf : IsOpenEmb f a) : (k ≫ f) a = ⊤ := by
  rw [comp_apply, hf.map_img, map_top]

/-- **Open embeddings compose.** -/
theorem comp {S : Chart} {k : S ⟶ T} {b : O T} (hk : IsOpenEmb k b) (hf : IsOpenEmb f a) :
    IsOpenEmb (k ≫ f) (hf.inv b) := by
  refine ⟨fun y => hf.inv (hk.inv y), fun y => hf.inv_mono (hk.inv_le y), fun y => ?_, fun c => ?_⟩
  · rw [comp_apply, hf.map_inv, hk.map_inv]
  · show hf.inv (hk.inv (k (f c))) = c ⊓ hf.inv b
    rw [hk.inv_map, hf.inv_inf, hf.inv_map, inf_assoc, inf_eq_right.mpr (hf.inv_le b)]

end IsOpenEmb

theorem isOpenEmb_id (U : Chart) : IsOpenEmb (𝟙 U) ⊤ :=
  ⟨fun y => y, fun _ => le_top, fun _ => rfl, fun b => (inf_top_eq b).symm⟩

/-- An isomorphism-like criterion: a map whose image is everything. -/
theorem IsOpenEmb.img_eq_top_iff {T U : Chart} {f : T ⟶ U} {a : O U} (hf : IsOpenEmb f a)
    {b : O U} (hb : b ≤ a) : f b = ⊤ ↔ b = a := by
  constructor
  · intro h
    rw [← inf_eq_left.mpr hb, ← hf.inv_map b, h, hf.inv_top]
  · rintro rfl
    exact hf.map_img

/-! ### Basic open embeddings -/

/-- An open embedding of spaces `ℝ → ℝ` gives an open embedding of locales. -/
theorem isOpenEmb_comap {ψ : ℝ → ℝ} (hψ : Topology.IsOpenEmbedding ψ) :
    IsOpenEmb (ofFrameHom (Opens.comap ⟨ψ, hψ.continuous⟩) : real ⟶ real)
      ⟨range ψ, hψ.isOpen_range⟩ := by
  refine ⟨fun V => ⟨ψ '' (V : Opens ℝ), hψ.isOpenMap _ (V : Opens ℝ).isOpen⟩, fun V => ?_, fun V => ?_,
    fun W => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · apply Opens.ext
    change ψ ⁻¹' (ψ '' _) = _
    exact preimage_image_eq _ hψ.injective
  · apply Opens.ext
    change ψ '' (ψ ⁻¹' _) = ((W : Opens ℝ) : Set ℝ) ∩ range ψ
    exact image_preimage_eq_inter_range

/-- The interval embedding `ℝ → ℝ` onto `(a, b)`. -/
def ivlEmb (a b : ℝ) (hab : a < b) : real ⟶ real :=
  ofFrameHom (Opens.comap ⟨ivlMap a b, continuous_ivlMap hab⟩)

theorem isOpenEmb_ivlEmb {a b : ℝ} (hab : a < b) : IsOpenEmb (ivlEmb a b hab) (oIoo a b) := by
  have h := isOpenEmb_comap (isOpenEmbedding_ivlMap hab)
  have e : (⟨range (ivlMap a b), (isOpenEmbedding_ivlMap hab).isOpen_range⟩ : Opens ℝ) = oIoo a b :=
    Opens.ext (range_ivlMap hab)
  rw [e] at h
  exact h

/-- The collar interval `((a, b), ⊥)` of `L_e`, for `0 ≤ a < b ≤ 1`. -/
def collarIvl (e : P) (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) : G e where
  V := oIoo a b
  d := ⊥
  hV := fun _ ht => ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩
  hd := bot_le
  glue h := absurd rfl h

/-- The collar-interval embedding `ℝ → L_e` onto `((a, b), ⊥)`. -/
def collarEmb {e : P} (he : e ≠ ⊥) (a b : ℝ) (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    real ⟶ endc e he :=
  ofFrameHom (collarHom e ⟨ivlMap a b, continuous_ivlMap hab⟩ fun x =>
    ⟨lt_of_le_of_lt ha (ivlMap_mem hab x).1, lt_of_lt_of_le (ivlMap_mem hab x).2 hb⟩)

theorem isOpenEmb_collarEmb {e : P} (he : e ≠ ⊥) {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    IsOpenEmb (collarEmb he a b hab ha hb) (collarIvl e a b ha hb) := by
  have hψ := isOpenEmbedding_ivlMap hab
  refine ⟨fun V => ⟨⟨ivlMap a b '' (V : Opens ℝ), hψ.isOpenMap _ (V : Opens ℝ).isOpen⟩, ⊥, ?_,
    bot_le, fun h => absurd rfl h⟩, fun V => ?_, fun V => ?_, fun y => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨lt_of_le_of_lt ha (ivlMap_mem hab x).1, lt_of_lt_of_le (ivlMap_mem hab x).2 hb⟩
  · refine ⟨?_, le_rfl⟩
    rintro _ ⟨x, -, rfl⟩
    exact ivlMap_mem hab x
  · apply Opens.ext
    change ivlMap a b ⁻¹' (ivlMap a b '' _) = _
    exact preimage_image_eq _ hψ.injective
  · apply G.ext
    · apply Opens.ext
      change ivlMap a b '' (ivlMap a b ⁻¹' _) = ((y.V : Opens ℝ) : Set ℝ) ∩ Ioo a b
      rw [image_preimage_eq_inter_range, range_ivlMap hab]
      rfl
    · exact (inf_bot_eq y.d).symm

/-- The initial piece `((0, ε), d)` of `L_e`, for `d ≤ e`, `0 < ε ≤ 1`. -/
def initIvl (e d : P) (hde : d ≤ e) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : G e where
  V := oIoo 0 ε
  d := d
  hV := fun _ ht => ⟨ht.1, lt_of_lt_of_le ht.2 hε1⟩
  hd := hde
  glue _ := ⟨ε, hε, subset_rfl⟩

/-- The collar component of the rescaling `L_d → L_e` by `ε`. -/
def rescaleV (ε : ℝ) (V : Opens ℝ) : Opens ℝ :=
  ⟨{t | t ∈ Ioo (0 : ℝ) 1 ∧ ε * t ∈ V}, isOpen_Ioo.inter (V.isOpen.preimage (continuous_const.mul continuous_id))⟩

/-- **The rescaling `L_d → L_e`** onto the initial piece `((0, ε), d)`. -/
def rescaleFun {d e : P} (_hd : d ≠ ⊥) (_hde : d ≤ e) (ε : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (y : G e) : G d where
  V := rescaleV ε y.V
  d := y.d ⊓ d
  hV := fun _ ht => ht.1
  hd := inf_le_right
  glue h := by
    have hy : y.d ≠ ⊥ := fun h' => h (by rw [h', bot_inf_eq])
    obtain ⟨δ, hδ, hsub⟩ := y.glue hy
    refine ⟨min 1 (δ / ε), lt_min one_pos (div_pos hδ hε), fun t ht => ⟨⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩, ?_⟩⟩
    apply hsub
    refine ⟨mul_pos hε ht.1, ?_⟩
    have := ht.2.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hε] at this
    linarith

def rescale {d e : P} (hd : d ≠ ⊥) (he : e ≠ ⊥) (hde : d ≤ e) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    endc d hd ⟶ endc e he where
  toFun := rescaleFun hd hde ε hε hε1
  map_inf' y z := G.ext (Opens.ext (by
    ext t
    change (t ∈ Ioo (0:ℝ) 1 ∧ ε * t ∈ (y.V ⊓ z.V : Opens ℝ)) ↔
      (t ∈ Ioo (0:ℝ) 1 ∧ ε * t ∈ y.V) ∧ (t ∈ Ioo (0:ℝ) 1 ∧ ε * t ∈ z.V)
    rw [Opens.mem_inf]
    tauto)) (by
    change (y.d ⊓ z.d) ⊓ d = (y.d ⊓ d) ⊓ (z.d ⊓ d)
    rw [inf_inf_distrib_right])
  map_top' := G.ext (Opens.ext (by
    ext t
    change (t ∈ Ioo (0:ℝ) 1 ∧ ε * t ∈ Ioo (0:ℝ) 1) ↔ t ∈ Ioo (0:ℝ) 1
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, mul_pos hε h.1, ?_⟩
      nlinarith [h.1, h.2])) (inf_eq_right.mpr hde)
  map_sSup' S := by
    apply G.ext
    · apply Opens.ext
      ext t
      change (t ∈ Ioo (0:ℝ) 1 ∧ ε * t ∈ (⨆ y ∈ S, y.V : Opens ℝ)) ↔
        t ∈ (⨆ z ∈ rescaleFun hd hde ε hε hε1 '' S, z.V : Opens ℝ)
      simp only [Opens.mem_iSup]
      constructor
      · rintro ⟨ht, y, hy, hty⟩
        exact ⟨_, ⟨y, hy, rfl⟩, ht, hty⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, ht, hty⟩
        exact ⟨ht, y, hy, hty⟩
    · change (⨆ y ∈ S, y.d) ⊓ d = ⨆ z ∈ rescaleFun hd hde ε hε hε1 '' S, z.d
      rw [iSup_image, iSup₂_inf_eq]
      rfl

@[simp] theorem rescale_apply_d {d e : P} (hd : d ≠ ⊥) (he : e ≠ ⊥) (hde : d ≤ e) (ε : ℝ) (hε)
    (hε1) (y : G e) : (rescale hd he hde ε hε hε1 y).d = y.d ⊓ d := rfl

theorem isOpenEmb_rescale {d e : P} (hd : d ≠ ⊥) (he : e ≠ ⊥) (hde : d ≤ e) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : IsOpenEmb (rescale hd he hde ε hε hε1) (initIvl e d hde ε hε hε1) := by
  have hmul : IsOpenMap (fun t : ℝ => ε * t) :=
    (Homeomorph.mulLeft₀ ε hε.ne').isOpenMap
  let inv : G d → G e := fun z => {
    V := ⟨(fun t => ε * t) '' (z.V : Set ℝ), hmul _ z.V.isOpen⟩
    d := z.d
    hV := by
      rintro _ ⟨t, ht, rfl⟩
      have := z.hV ht
      exact ⟨mul_pos hε this.1, by nlinarith [this.1, this.2]⟩
    hd := z.hd.trans hde
    glue := fun h => by
      obtain ⟨δ, hδ, hsub⟩ := z.glue h
      refine ⟨ε * δ, mul_pos hε hδ, fun t ht => ⟨t / ε, hsub ⟨div_pos ht.1 hε, ?_⟩, ?_⟩⟩
      · rw [div_lt_iff₀ hε]; linarith [ht.2]
      · field_simp }
  refine ⟨inv, fun z => ⟨?_, z.hd⟩, fun z => ?_, fun y => ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    have := z.hV ht
    exact ⟨mul_pos hε this.1, by nlinarith [this.1, this.2]⟩
  · apply G.ext
    · apply Opens.ext
      ext t
      change (t ∈ Ioo (0:ℝ) 1 ∧ ε * t ∈ (fun t => ε * t) '' (z.V : Set ℝ)) ↔ t ∈ z.V
      constructor
      · rintro ⟨-, s, hs, hst⟩
        have : s = t := mul_left_cancel₀ hε.ne' hst
        rw [← this]
        exact hs
      · intro ht
        exact ⟨z.hV ht, t, ht, rfl⟩
    · exact inf_eq_left.mpr z.hd
  · apply G.ext
    · apply Opens.ext
      ext s
      change s ∈ (fun t => ε * t) '' {t | t ∈ Ioo (0:ℝ) 1 ∧ ε * t ∈ y.V} ↔ s ∈ y.V ∧ s ∈ Ioo 0 ε
      constructor
      · rintro ⟨t, ⟨ht, hty⟩, rfl⟩
        exact ⟨hty, mul_pos hε ht.1, by nlinarith [ht.1, ht.2]⟩
      · rintro ⟨hs, hs0, hsε⟩
        refine ⟨s / ε, ⟨⟨div_pos hs0 hε, ?_⟩, ?_⟩, ?_⟩
        · rw [div_lt_iff₀ hε]; linarith
        · rwa [mul_div_cancel₀ s hε.ne']
        · field_simp
    · rfl

/-! ### The chart basis -/

/-- The images of open embeddings below `b`. -/
def basicBelow {U : Chart} (b : O U) : Set (O U) :=
  {a | a ≤ b ∧ ∃ (T : Chart) (f : T ⟶ U), IsOpenEmb f a}

/-- **Chart basis.** Every open of a chart is the join of the images of the open embeddings
of charts that it contains. -/
theorem basis (U : Chart) (b : O U) : b = sSup (basicBelow b) := by
  apply le_antisymm _ (sSup_le fun a ha => ha.1)
  cases U with
  | pt =>
    by_cases hb : (b : Prop)
    · have h1 : (⊤ : O pt) ∈ basicBelow b := ⟨fun _ => hb, pt, 𝟙 pt, isOpen_id_pt⟩
      exact fun _ => le_sSup h1 trivial
    · intro h
      exact absurd h hb
  | real =>
    conv_lhs => rw [opens_eq_iSup_oIoo b]
    refine iSup_le fun q => iSup_le fun r => iSup_le fun hqr => ?_
    rcases le_or_gt (r : ℝ) q with hle | hlt
    · intro x hx
      exact absurd (lt_trans hx.1 hx.2) (not_lt.mpr hle)
    · exact le_sSup ⟨hqr, real, ivlEmb q r hlt, isOpenEmb_ivlEmb hlt⟩
  | endc e he =>
    have hcol : ∀ (q r : ℚ), Ioo (q : ℝ) r ⊆ (b.V : Set ℝ) → (q : ℝ) < r →
        tHom e (oIoo q r) ≤ sSup (basicBelow (U := endc e he) b) := by
      intro q r hqr hlt
      obtain ⟨t, ht⟩ : (Ioo (q : ℝ) r).Nonempty := nonempty_Ioo.mpr hlt
      have hq : (0 : ℝ) ≤ q := by
        by_contra h
        rw [not_le] at h
        obtain ⟨s, hs1, hs2⟩ := exists_between (lt_min h hlt)
        have := b.hV (hqr ⟨hs1, hs2.trans_le (min_le_right _ _)⟩)
        linarith [this.1, hs2.trans_le (min_le_left _ _)]
      have hr : (r : ℝ) ≤ 1 := by
        by_contra h
        rw [not_le] at h
        obtain ⟨s, hs1, hs2⟩ := exists_between (show max (1:ℝ) q < r from max_lt h hlt)
        have := b.hV (hqr ⟨(le_max_right _ _).trans_lt hs1, hs2⟩)
        linarith [this.2, (le_max_left (1:ℝ) q).trans_lt hs1]
      have heq : tHom e (oIoo q r) = collarIvl e q r hq hr := by
        apply G.ext
        · apply Opens.ext
          ext s
          change s ∈ Ioo (q:ℝ) r ∧ s ∈ Ioo (0:ℝ) 1 ↔ s ∈ Ioo (q:ℝ) r
          constructor
          · exact fun h => h.1
          · intro h
            exact ⟨h, lt_of_le_of_lt hq h.1, lt_of_lt_of_le h.2 hr⟩
        · exact endVal_of_not_mem (fun h0 => absurd h0.1 (not_lt.mpr hq))
      rw [heq]
      exact le_sSup ⟨⟨hqr, bot_le⟩, real, collarEmb he q r hlt hq hr, isOpenEmb_collarEmb he hlt hq hr⟩
    -- the collar part
    have hV : tHom e b.V ≤ sSup (basicBelow (U := endc e he) b) := by
      conv_lhs => rw [opens_eq_iSup_oIoo b.V]
      rw [map_iSup]
      refine iSup_le fun q => ?_
      rw [map_iSup]
      refine iSup_le fun r => ?_
      rw [map_iSup]
      refine iSup_le fun hqr => ?_
      rcases le_or_gt (r : ℝ) q with hle | hlt
      · have : oIoo (q : ℝ) r = ⊥ := Opens.ext (Ioo_eq_empty (not_lt.mpr hle))
        rw [this, map_bot]
        exact bot_le
      · exact hcol q r hqr hlt
    by_cases hd : b.d = ⊥
    · conv_lhs => rw [eq_tHom_of_d_eq_bot hd]
      exact hV
    · obtain ⟨ε, hε, hsub⟩ := b.glue hd
      have hε' : 0 < min ε 1 := lt_min hε one_pos
      have hsub' : Ioo 0 (min ε 1) ⊆ (b.V : Set ℝ) := fun t ht => hsub ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
      have hinit : initIvl e b.d b.hd (min ε 1) hε' (min_le_right _ _) ∈
          basicBelow (U := endc e he) b :=
        ⟨⟨fun t ht => hsub' ht, le_rfl⟩, endc b.d hd, rescale hd he b.hd _ hε' (min_le_right _ _),
          isOpenEmb_rescale hd he b.hd _ hε' (min_le_right _ _)⟩
      have hb : b = tHom e b.V ⊔ initIvl e b.d b.hd (min ε 1) hε' (min_le_right _ _) := by
        apply G.ext
        · apply Opens.ext
          ext t
          change t ∈ (b.V : Set ℝ) ↔ (t ∈ (b.V : Set ℝ) ∧ t ∈ Ioo (0:ℝ) 1) ∨ t ∈ Ioo 0 (min ε 1)
          constructor
          · intro ht
            exact Or.inl ⟨ht, b.hV ht⟩
          · rintro (⟨ht, -⟩ | ht)
            · exact ht
            · exact hsub' ht
        · change b.d = endVal e b.V ⊔ b.d
          rw [endVal_of_not_mem (fun h0 => lt_irrefl _ (b.hV h0).1), bot_sup_eq]
      conv_lhs => rw [hb]
      exact sup_le hV (le_sSup hinit)
where
  isOpen_id_pt : IsOpenEmb (𝟙 pt) ⊤ := isOpenEmb_id pt

/-! ### Paths between points -/

/-- **Any two points of a chart are joined by a path `ℝ ⟶ U`.** -/
theorem exists_path (U : Chart) (p q : pt ⟶ U) :
    ∃ γ : real ⟶ U, ptAt 0 ≫ γ = p ∧ ptAt 1 ≫ γ = q := by
  cases U with
  | pt =>
    exact ⟨toPt real, (toPt_eq _).trans (toPt_eq p).symm, (toPt_eq _).trans (toPt_eq q).symm⟩
  | real =>
    obtain ⟨x, rfl⟩ := real_point p
    obtain ⟨y, rfl⟩ := real_point q
    let g : C(ℝ, ℝ) := ⟨fun s => x + s * (y - x), by fun_prop⟩
    refine ⟨ofFrameHom (Opens.comap g), ?_, ?_⟩
    · ext W
      change g 0 ∈ W ↔ x ∈ W
      simp [g]
    · ext W
      change g 1 ∈ W ↔ y ∈ W
      simp [g]
  | endc e he =>
    obtain ⟨x, hx, rfl⟩ := end_point p
    obtain ⟨y, hy, rfl⟩ := end_point q
    let g : C(ℝ, ℝ) := ⟨fun s => x + max 0 (min 1 s) * (y - x), by fun_prop⟩
    have hg : ∀ s, g s ∈ Ioo (0 : ℝ) 1 := by
      intro s
      have h0 : 0 ≤ max 0 (min 1 s) := le_max_left _ _
      have h1 : max 0 (min 1 s) ≤ 1 := max_le zero_le_one (min_le_left _ _)
      change x + max 0 (min 1 s) * (y - x) ∈ Ioo (0 : ℝ) 1
      set l := max 0 (min 1 s)
      have key : x + l * (y - x) = (1 - l) * x + l * y := by ring
      rw [key]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left (min_le_left x y) (sub_nonneg.mpr h1),
          mul_le_mul_of_nonneg_left (min_le_right x y) h0, lt_min hx.1 hy.1]
      · nlinarith [mul_le_mul_of_nonneg_left (le_max_left x y) (sub_nonneg.mpr h1),
          mul_le_mul_of_nonneg_left (le_max_right x y) h0, max_lt hx.2 hy.2]
    refine ⟨ofFrameHom (collarHom e g hg), ?_, ?_⟩
    · ext z
      change g 0 ∈ z.V ↔ x ∈ z.V
      simp [g]
    · ext z
      change g 1 ∈ z.V ↔ y ∈ z.V
      simp [g]

end Chart

end PointlessEnd
