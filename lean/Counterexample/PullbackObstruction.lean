import Cohesion.Pullbacks
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The representable obstruction to local connectedness

`PreservesPullbacksAlong L R` is the pullback formulation of the indexed
condition: `L` preserves pullbacks along maps in the image of `R`.
For the leftmost adjunction of a connected essential geometric morphism,
this is the usual local-connectedness condition.  No finite completeness
of the indexing categories is assumed in the transfer lemmas below.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Presheaf

namespace Counterexample

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {S : Type u₃} [Category.{v₃} S]

-- Compatibility names for the shared cohesion API.
export Cohesion (PreservesPullbacksAlong isPullback_map_of_natIso)

namespace PreservesPullbacksAlong
export Cohesion.PreservesPullbacksAlong (precomp of_right_iso)
end PreservesPullbacksAlong

/-- The Garner--Streicher representable argument, in a form that only needs
the one pullback under consideration.  In the intended application `J` and
`K` are Yoneda embeddings. -/
theorem reflection_pullback_of_presheaf
    {E : Type u₄} [Category.{v₄} E]
    (a : C ⥤ D) (i : D ⥤ C)
    (J : C ⥤ E) (K : D ⥤ S) (L : E ⥤ S) (R : S ⥤ E)
    (eL : J ⋙ L ≅ a ⋙ K) (eR : i ⋙ J ≅ K ⋙ R)
    (h : PreservesPullbacksAlong L R)
    {A B : D} (f : A ⟶ B) {P X : C}
    (p : P ⟶ X) (q : P ⟶ i.obj A) (g : X ⟶ i.obj B)
    [PreservesLimit (cospan g (i.map f)) J]
    [ReflectsLimit (cospan (a.map g) (a.map (i.map f))) K]
    (sq : IsPullback p q g (i.map f)) :
    IsPullback (a.map p) (a.map q) (a.map g) (a.map (i.map f)) := by
  have h' : PreservesPullbacksAlong L (i ⋙ J) :=
    PreservesPullbacksAlong.of_right_iso (h.precomp K) eR.symm
  have hs := h' f (J.map p) (J.map q) (J.map g) (sq.map J)
  have ht := isPullback_map_of_natIso eL hs
  exact ht.of_map K (by simpa only [← a.map_comp] using congrArg a.map sq.w)

theorem not_preservesPullbacksAlong_of_reflection
    {E : Type u₄} [Category.{v₄} E]
    (a : C ⥤ D) (i : D ⥤ C)
    (J : C ⥤ E) (K : D ⥤ S) (L : E ⥤ S) (R : S ⥤ E)
    (eL : J ⋙ L ≅ a ⋙ K) (eR : i ⋙ J ≅ K ⋙ R)
    {A B : D} (f : A ⟶ B) {P X : C}
    (p : P ⟶ X) (q : P ⟶ i.obj A) (g : X ⟶ i.obj B)
    [PreservesLimit (cospan g (i.map f)) J]
    [ReflectsLimit (cospan (a.map g) (a.map (i.map f))) K]
    (sq : IsPullback p q g (i.map f))
    (bad : ¬ IsPullback (a.map p) (a.map q) (a.map g) (a.map (i.map f))) :
    ¬ PreservesPullbacksAlong L R := by
  intro h
  exact bad (reflection_pullback_of_presheaf a i J K L R eL eR h f p q g sq)

section Presheaves

universe u
variable {A B : Type u} [SmallCategory A] [SmallCategory B]

/-- Left Kan extension takes representables to the reflected representables. -/
def yonedaPiecesIso (a : B ⥤ A) :
    yoneda ⋙ (a.op.lan : (Bᵒᵖ ⥤ Type u) ⥤ (Aᵒᵖ ⥤ Type u)) ≅ a ⋙ yoneda :=
  isoWhiskerRight uliftYonedaIsoYoneda.symm a.op.lan ≪≫
    (compULiftYonedaIsoULiftYonedaCompLan a).symm ≪≫
    isoWhiskerLeft a uliftYonedaIsoYoneda

/-- The paper's local-connectedness condition for the presheaf adjunction. -/
def PresheafLocallyConnected (a : B ⥤ A) : Prop :=
  PreservesPullbacksAlong
    (a.op.lan : (Bᵒᵖ ⥤ Type u) ⥤ (Aᵒᵖ ⥤ Type u))
    ((whiskeringLeft Bᵒᵖ Aᵒᵖ (Type u)).obj a.op)

/-- A failed existing pullback of a reflection is a genuine obstruction
to local connectedness of its presheaf geometric morphism. -/
theorem presheaf_not_locallyConnected
    (a : B ⥤ A) (i : A ⥤ B) (adj : a ⊣ i)
    {A₀ A₁ : A} (f : A₀ ⟶ A₁) {P X : B}
    (p : P ⟶ X) (q : P ⟶ i.obj A₀) (g : X ⟶ i.obj A₁)
    (sq : IsPullback p q g (i.map f))
    (bad : ¬ IsPullback (a.map p) (a.map q) (a.map g) (a.map (i.map f))) :
    ¬ PresheafLocallyConnected a :=
  not_preservesPullbacksAlong_of_reflection a i yoneda yoneda _ _
    (yonedaPiecesIso a) adj.compYonedaIso f p q g sq bad

end Presheaves

end Counterexample
