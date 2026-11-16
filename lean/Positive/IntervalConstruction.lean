import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Attaching intervals along a subobject

The construction uses a pushout `(B + B) ⨿[Q + Q] I`, where `I → Q` has two
sections. A colimit-preserving functor that inverts `I → Q` turns this into
the double pushout `B ⨿[Q] B`.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
universe v u v' u'
namespace Positive.IntervalConstruction
variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  {Q B I : C} (m : Q ⟶ B) (e₀ e₁ : Q ⟶ I)

abbrev obj := pushout (coprod.map m m) (coprod.desc e₀ e₁)

def vertex₀ : B ⟶ obj m e₀ e₁ := coprod.inl ≫ pushout.inl _ _
def vertex₁ : B ⟶ obj m e₀ e₁ := coprod.inr ≫ pushout.inl _ _
def middle : I ⟶ obj m e₀ e₁ := pushout.inr _ _

@[reassoc]
lemma attach₀ : m ≫ vertex₀ m e₀ e₁ = e₀ ≫ middle m e₀ e₁ := by
  have h := congrArg (fun k => coprod.inl ≫ k)
    (pushout.condition (f := coprod.map m m) (g := coprod.desc e₀ e₁))
  simpa [vertex₀, middle] using h

@[reassoc]
lemma attach₁ : m ≫ vertex₁ m e₀ e₁ = e₁ ≫ middle m e₀ e₁ := by
  have h := congrArg (fun k => coprod.inr ≫ k)
    (pushout.condition (f := coprod.map m m) (g := coprod.desc e₀ e₁))
  simpa [vertex₁, middle] using h

/-- The intervals and vertices jointly cover the pushout. -/
instance cover_epi :
    Epi (coprod.desc (coprod.desc (vertex₀ m e₀ e₁) (vertex₁ m e₀ e₁))
      (middle m e₀ e₁)) := by
  have h : coprod.desc (vertex₀ m e₀ e₁) (vertex₁ m e₀ e₁) = pushout.inl _ _ := by
    ext <;> simp [vertex₀, vertex₁]
  rw [h]
  exact epi_coprod_to_pushout _ _

variable (r : I ⟶ Q) (h₀ : e₀ ≫ r = 𝟙 Q) (h₁ : e₁ ≫ r = 𝟙 Q)

/-- The entire attachment lies over the original object `B`. -/
def projection : obj m e₀ e₁ ⟶ B :=
  pushout.desc (coprod.desc (𝟙 B) (𝟙 B)) (r ≫ m) (by
    ext <;> simp [← Category.assoc, h₀, h₁])

@[reassoc (attr := simp)]
lemma vertex₀_projection : vertex₀ m e₀ e₁ ≫ projection m e₀ e₁ r h₀ h₁ = 𝟙 B := by
  simp [vertex₀, projection]

@[reassoc (attr := simp)]
lemma vertex₁_projection : vertex₁ m e₀ e₁ ≫ projection m e₀ e₁ r h₀ h₁ = 𝟙 B := by
  simp [vertex₁, projection]

@[reassoc (attr := simp)]
lemma middle_projection : middle m e₀ e₁ ≫ projection m e₀ e₁ r h₀ h₁ = r ≫ m := by
  simp [middle, projection]

end Positive.IntervalConstruction

namespace Positive
variable {C : Type u} [Category.{v} C]

/-- Compressing the middle of an interval-attachment pushout to its base
produces a double pushout. This formulation is independent of chosen colimits. -/
theorem doublePushout_of_attachment {Q B U V I X : C}
    (q₀ q₁ : Q ⟶ U) (b₀ b₁ : B ⟶ V) (m : Q ⟶ B)
    (a : U ⟶ V) (e : U ⟶ I) (l : V ⟶ X) (j : I ⟶ X) (i : Q ⟶ I) [IsIso i]
    (hq : IsColimit (BinaryCofan.mk q₀ q₁))
    (hb : IsColimit (BinaryCofan.mk b₀ b₁))
    (ha₀ : q₀ ≫ a = m ≫ b₀) (ha₁ : q₁ ≫ a = m ≫ b₁)
    (he₀ : q₀ ≫ e = i) (he₁ : q₁ ≫ e = i) (sq : IsPushout a e l j) :
    IsPushout m m (b₀ ≫ l) (b₁ ≫ l) := by
  have hm₀ : m ≫ b₀ ≫ l = i ≫ j := by
    rw [← Category.assoc, ← ha₀, Category.assoc, sq.w, ← Category.assoc, he₀]
  have hm₁ : m ≫ b₁ ≫ l = i ≫ j := by
    rw [← Category.assoc, ← ha₁, Category.assoc, sq.w, ← Category.assoc, he₁]
  refine IsPushout.mk' (hm₀.trans hm₁.symm) ?_ ?_
  · intro T f g h₀ h₁
    apply sq.hom_ext
    · apply BinaryCofan.IsColimit.hom_ext hb
      · simpa only [BinaryCofan.mk_inl, Category.assoc] using h₀
      · simpa only [BinaryCofan.mk_inr, Category.assoc] using h₁
    · apply (cancel_epi i).mp
      calc
        i ≫ j ≫ f = (m ≫ b₀ ≫ l) ≫ f := by rw [hm₀, Category.assoc]
        _ = (m ≫ b₀ ≫ l) ≫ g := by
          simpa only [Category.assoc] using congrArg (fun k => m ≫ k) h₀
        _ = i ≫ j ≫ g := by rw [hm₀, Category.assoc]
  · intro T f g hfg
    let u := BinaryCofan.IsColimit.desc hb f g
    let v := inv i ≫ m ≫ f
    have hu₀ : b₀ ≫ u = f := BinaryCofan.IsColimit.inl_desc hb f g
    have hu₁ : b₁ ≫ u = g := BinaryCofan.IsColimit.inr_desc hb f g
    have huv : a ≫ u = e ≫ v := by
      apply BinaryCofan.IsColimit.hom_ext hq
      · change q₀ ≫ a ≫ u = q₀ ≫ e ≫ v
        rw [← Category.assoc, ha₀, Category.assoc, hu₀,
          ← Category.assoc, he₀]
        simp [v]
      · change q₁ ≫ a ≫ u = q₁ ≫ e ≫ v
        rw [← Category.assoc, ha₁, Category.assoc, hu₁,
          ← Category.assoc, he₁]
        simpa [v] using hfg.symm
    refine ⟨sq.desc u v huv, ?_, ?_⟩
    · simpa only [Category.assoc, sq.inl_desc] using hu₀
    · simpa only [Category.assoc, sq.inl_desc] using hu₁

end Positive

namespace Positive.IntervalConstruction
variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  {D : Type u'} [Category.{v'} D]
  {Q B I : C} (m : Q ⟶ B) (e₀ e₁ : Q ⟶ I) (r : I ⟶ Q)
  (h₀ : e₀ ≫ r = 𝟙 Q) (h₁ : e₁ ≫ r = 𝟙 Q)
  (F : C ⥤ D) [PreservesColimitsOfSize.{0,0} F] [IsIso (F.map r)]

include r h₀ h₁ in
/-- Collapsing the interval fibers identifies precisely the two vertices over Q. -/
theorem map_isPushout : IsPushout (F.map m) (F.map m)
    (F.map (vertex₀ m e₀ e₁)) (F.map (vertex₁ m e₀ e₁)) := by
  have he₀ : F.map e₀ = inv (F.map r) := by
    apply (cancel_mono (F.map r)).mp
    simp [← F.map_comp, h₀]
  have he₁ : F.map e₁ = F.map e₀ := by
    apply (cancel_mono (F.map r)).mp
    simp [← F.map_comp, h₀, h₁]
  have : IsIso (F.map e₀) := by rw [he₀]; infer_instance
  simpa only [vertex₀, vertex₁, F.map_comp] using
    doublePushout_of_attachment
      (F.map (coprod.inl : Q ⟶ Q ⨿ Q)) (F.map coprod.inr)
      (F.map (coprod.inl : B ⟶ B ⨿ B)) (F.map coprod.inr) (F.map m)
      (F.map (coprod.map m m)) (F.map (coprod.desc e₀ e₁))
      (F.map (pushout.inl _ _)) (F.map (pushout.inr _ _)) (F.map e₀)
      (isColimitOfHasBinaryCoproductOfPreservesColimit F Q Q)
      (isColimitOfHasBinaryCoproductOfPreservesColimit F B B)
      (by simp only [← F.map_comp, coprod.inl_map])
      (by simp only [← F.map_comp, coprod.inr_map])
      (by simp only [← F.map_comp, coprod.inl_desc])
      (by simpa only [← F.map_comp, coprod.inr_desc] using he₁)
      ((IsPushout.of_hasPushout (coprod.map m m) (coprod.desc e₀ e₁)).map F)

end Positive.IntervalConstruction
