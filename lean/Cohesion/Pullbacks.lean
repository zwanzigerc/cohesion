import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pullback preservation along a functor

The indexed pullback condition shared by the positive cohesion theorem and
its counterexample. No finite completeness assumption is needed: it concerns
each existing pullback separately.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Cohesion

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {S : Type u₃} [Category.{v₃} S]

/-- Preservation of each existing pullback along a morphism in the image of `R`. -/
def PreservesPullbacksAlong (L : C ⥤ D) (R : S ⥤ C) : Prop :=
  ∀ {A B : S} (f : A ⟶ B) {P X : C}
    (p : P ⟶ X) (q : P ⟶ R.obj A) (g : X ⟶ R.obj B),
    IsPullback p q g (R.map f) →
      IsPullback (L.map p) (L.map q) (L.map g) (L.map (R.map f))

namespace PreservesPullbacksAlong

theorem precomp {T : Type u₄} [Category.{v₄} T]
    {L : C ⥤ D} {R : S ⥤ C} (h : PreservesPullbacksAlong L R)
    (F : T ⥤ S) : PreservesPullbacksAlong L (F ⋙ R) := by
  intro A B f P X p q g sq
  exact h (F.map f) p q g sq

/-- The condition does not depend on the chosen isomorphic embedding. -/
theorem of_right_iso {L : C ⥤ D} {R R' : S ⥤ C}
    (h : PreservesPullbacksAlong L R) (e : R ≅ R') :
    PreservesPullbacksAlong L R' := by
  intro A B f P X p q g sq
  have sq' : IsPullback p (q ≫ e.inv.app A) (g ≫ e.inv.app B) (R.map f) := by
    apply sq.of_iso (Iso.refl _) (Iso.refl _) (e.app A).symm (e.app B).symm
    · simp
    · simp
    · simp
    · exact e.inv.naturality f
  have hs := h f p (q ≫ e.inv.app A) (g ≫ e.inv.app B) sq'
  apply hs.of_iso (Iso.refl _) (Iso.refl _) (L.mapIso (e.app A)) (L.mapIso (e.app B))
  · simp
  · simp only [Functor.mapIso_hom, Iso.app_hom, Iso.refl_hom, Category.id_comp, ← L.map_comp,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  · simp only [Functor.mapIso_hom, Iso.app_hom, Iso.refl_hom, Category.id_comp, ← L.map_comp,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  · simpa only [Functor.mapIso_hom, Iso.app_hom, ← L.map_comp] using
      congrArg L.map (e.hom.naturality f)

end PreservesPullbacksAlong

/-- Transport preservation of an individual pullback across a natural isomorphism. -/
theorem isPullback_map_of_natIso {F G : C ⥤ D} (e : F ≅ G)
    {P X Y Z : C} {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) :
    IsPullback (G.map p) (G.map q) (G.map f) (G.map g) := by
  exact h.of_iso (e.app P) (e.app X) (e.app Y) (e.app Z)
    (e.hom.naturality p) (e.hom.naturality q)
    (e.hom.naturality f) (e.hom.naturality g)

end Cohesion
