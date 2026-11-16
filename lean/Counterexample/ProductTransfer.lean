import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Sifted
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Finite products and left Kan extension on presheaves

The left Kan extension of a finite-product-preserving functor between small
categories preserves finite products of set-valued presheaves.  The source
category needs finite products, but neither category needs all finite limits.

The pointwise Kan-extension formula expresses evaluation as a colimit over a
costructured-arrow category.  These indexing categories have finite coproducts,
and hence are sifted.  The claim follows because sifted colimits of sets commute
with finite products.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Precohesion.PresheafReflection

variable {A B : Type u} [SmallCategory A] [SmallCategory B]

/-- The comma categories computing the presheaf left Kan extension are sifted. -/
theorem isSifted_costructuredArrow_op (a : B ⥤ A)
    [HasFiniteProducts B] [PreservesFiniteProducts a] (X : Aᵒᵖ) :
    IsSifted (CostructuredArrow a.op X) := by
  let : PreservesFiniteCoproducts a.op := preservesFiniteCoproducts_op a
  let : HasInitial (CostructuredArrow a.op X) := inferInstance
  let : Nonempty (CostructuredArrow a.op X) := ⟨⊥_ _⟩
  infer_instance

/-- Finite-product preservation passes to left Kan extension on presheaves. -/
theorem preservesFiniteProducts_lan_op (a : B ⥤ A)
    [HasFiniteProducts B] [PreservesFiniteProducts a] :
    PreservesFiniteProducts (a.op.lan : (Bᵒᵖ ⥤ Type u) ⥤ (Aᵒᵖ ⥤ Type u)) where
  preserves n := by
    apply preservesLimitsOfShape_of_evaluation
    intro X
    let : IsSifted (CostructuredArrow a.op X) :=
      isSifted_costructuredArrow_op a X
    exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim (Type u) a.op X).symm

end Precohesion.PresheafReflection
