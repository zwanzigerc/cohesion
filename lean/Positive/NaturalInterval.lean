import Positive.IntervalConstruction
import ToposPort.DoublePushout

/-! # The natural comparison on an interval attachment

These identities relate the two images of the actual pushout under a natural
transformation whose components on the vertices and attachment base are invertible.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
universe v u v' u'
namespace Positive.NaturalInterval
open IntervalConstruction
variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  {D : Type u'} [Category.{v'} D]
  {Q B I : C} (m : Q ⟶ B) (e₀ e₁ : Q ⟶ I) (r : I ⟶ Q)
  (h₀ : e₀ ≫ r = 𝟙 Q) (h₁ : e₁ ≫ r = 𝟙 Q)
  (F G : C ⥤ D) (α : G ⟶ F) [IsIso (α.app Q)] [IsIso (α.app B)]

abbrev k₀ : G.obj B ⟶ F.obj (obj m e₀ e₁) := α.app B ≫ F.map (vertex₀ m e₀ e₁)
abbrev k₁ : G.obj B ⟶ F.obj (obj m e₀ e₁) := α.app B ≫ F.map (vertex₁ m e₀ e₁)
abbrev baseMap : F.obj (obj m e₀ e₁) ⟶ G.obj B :=
  F.map (projection m e₀ e₁ r h₀ h₁) ≫ inv (α.app B)

@[reassoc (attr := simp)]
lemma k₀_baseMap : k₀ m e₀ e₁ F G α ≫ baseMap m e₀ e₁ r h₀ h₁ F G α = 𝟙 _ := by
  simp only [k₀, baseMap, Category.assoc]
  rw [← F.map_comp_assoc, vertex₀_projection, F.map_id, Category.id_comp]
  exact IsIso.hom_inv_id _

@[reassoc (attr := simp)]
lemma k₁_baseMap : k₁ m e₀ e₁ F G α ≫ baseMap m e₀ e₁ r h₀ h₁ F G α = 𝟙 _ := by
  simp only [k₁, baseMap, Category.assoc]
  rw [← F.map_comp_assoc, vertex₁_projection, F.map_id, Category.id_comp]
  exact IsIso.hom_inv_id _

@[reassoc]
lemma comparison_baseMap : α.app (obj m e₀ e₁) ≫ baseMap m e₀ e₁ r h₀ h₁ F G α =
    G.map (projection m e₀ e₁ r h₀ h₁) := by
  rw [baseMap, ← Category.assoc, ← α.naturality, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

@[reassoc]
lemma vertex₀_comparison : G.map (vertex₀ m e₀ e₁) ≫ α.app (obj m e₀ e₁) =
    k₀ m e₀ e₁ F G α := α.naturality _

@[reassoc]
lemma vertex₁_comparison : G.map (vertex₁ m e₀ e₁) ≫ α.app (obj m e₀ e₁) =
    k₁ m e₀ e₁ F G α := α.naturality _

include α in
lemma map_mono [Mono (G.map m)] : Mono (F.map m) := by
  have h : F.map m = inv (α.app Q) ≫ G.map m ≫ α.app B := by
    rw [α.naturality, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

include r h₀ h₁ in
/-- The two images of the vertices agree precisely along the image of `m`. -/
theorem vertices_isPullback [HasPullbacks D] [HasSubobjectClassifier D]
    [PreservesColimitsOfSize.{0,0} F] [IsIso (F.map r)] [Mono (G.map m)] :
    IsPullback (G.map m) (G.map m) (k₀ m e₀ e₁ F G α) (k₁ m e₀ e₁ F G α) := by
  have : Mono (F.map m) := map_mono m F G α
  have sq := ToposPort.doublePushout_isPullback_of_classifier (F.map m)
    (IntervalConstruction.map_isPushout m e₀ e₁ r h₀ h₁ F)
  have hm : F.map m ≫ inv (α.app B) = inv (α.app Q) ≫ G.map m := by
    apply (cancel_epi (α.app Q)).mp
    rw [← Category.assoc, ← α.naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, IsIso.hom_inv_id_assoc]
  exact sq.of_iso (asIso (α.app Q)).symm (asIso (α.app B)).symm
    (asIso (α.app B)).symm (Iso.refl _) hm hm
    (by simp [k₀]) (by simp [k₁])

end Positive.NaturalInterval
