import Cohesion.Precohesive
import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-! # Continuity and powers of the canonical points-to-pieces map -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

namespace Cohesion

universe v u₁ u₂
variable {E : Type u₁} {S : Type u₂} [Category.{v} E] [Category.{v} S]
  [CartesianMonoidalCategory E] [CartesianMonoidalCategory S]
  [MonoidalClosed E] [MonoidalClosed S]

/-- The canonical Continuity comparison for a product-preserving left adjoint
whose right adjoint is fully faithful. This definition needs no Nullstellensatz
or extra adjoints, so it also applies directly to presheaf reflections. -/
def continuityComparison {L : E ⥤ S} {R : S ⥤ E} (adj : L ⊣ R)
    [R.Full] [R.Faithful] [PreservesFiniteProducts L] (X : E) (A : S) :
    L.obj ((ihom (R.obj A)).obj X) ⟶ (ihom A).obj (L.obj X) :=
  (expComparison L (R.obj A)).natTrans.app X ≫
    (MonoidalClosed.pre (inv (adj.counit.app A))).app _

namespace PrecohesiveMorphism

variable (p : Cohesion.PrecohesiveMorphism E S)

local instance : p.discrete.Full := p.discreteFullyFaithful.full
local instance : p.discrete.Faithful := p.discreteFullyFaithful.faithful
local instance : PreservesFiniteProducts p.pieces := p.piecesPreservesFiniteProducts

/-- The canonical transformation from points to pieces. -/
def theta : p.points ⟶ p.pieces := p.adjunctions.leftTriple.rightToLeft

instance theta_epi (X : E) : Epi ((theta p).app X) := p.nullstellensatz X

/-- Continuity, defined by evaluation using the product comparison and the
counit identification `Π Δ A ≅ A`. -/
def continuityComparison (X : E) (A : S) :
    p.pieces.obj ((ihom (p.discrete.obj A)).obj X) ⟶
      (ihom A).obj (p.pieces.obj X) :=
  Cohesion.continuityComparison p.adjunctions.adj₁ X A

/-- Epic Continuity, with respect to the canonical comparison just defined. -/
def EpicContinuity : Prop := ∀ (X : E) (A : S), Epi (continuityComparison p X A)


/-- Monic Continuity for the canonical comparison. -/
def MonicContinuity : Prop := ∀ (X : E) (A : S), Mono (continuityComparison p X A)

end PrecohesiveMorphism

section NaturalTransformation
variable (F G : E ⥤ S) (α : F ⟶ G)

omit [MonoidalClosed E] [MonoidalClosed S] in
/-- Every natural transformation between functors respects the canonical
comparison with products. -/
@[reassoc]
theorem prodComparison_natTrans (A B : E) :
    α.app (A ⊗ B) ≫ CartesianMonoidalCategory.prodComparison G A B =
      CartesianMonoidalCategory.prodComparison F A B ≫ (α.app A ⊗ₘ α.app B) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst, tensorHom_fst, CartesianMonoidalCategory.prodComparison_fst_assoc]
    exact (α.naturality (fst A B)).symm
  · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_snd, tensorHom_snd, CartesianMonoidalCategory.prodComparison_snd_assoc]
    exact (α.naturality (snd A B)).symm

variable [PreservesLimitsOfShape (Discrete WalkingPair) F]
  [PreservesLimitsOfShape (Discrete WalkingPair) G]

omit [MonoidalClosed E] [MonoidalClosed S] in
@[reassoc]
theorem inv_prodComparison_natTrans (A B : E) :
    (α.app A ⊗ₘ α.app B) ≫ inv (CartesianMonoidalCategory.prodComparison G A B) =
      inv (CartesianMonoidalCategory.prodComparison F A B) ≫ α.app (A ⊗ B) := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, ← prodComparison_natTrans]
  simp

/-- Naturality of exponential comparison in a transformation between
product-preserving functors. -/
@[reassoc]
theorem expComparison_natTrans (A X : E) :
    α.app ((ihom A).obj X) ≫ (expComparison G A).natTrans.app X ≫
      (MonoidalClosed.pre (α.app A)).app (G.obj X) =
    (expComparison F A).natTrans.app X ≫ (ihom (F.obj A)).map (α.app X) := by
  rw [← Category.assoc]
  apply MonoidalClosed.uncurry_injective
  rw [uncurry_pre_app, uncurry_natural_left, uncurry_natural_right,
    uncurry_expComparison, uncurry_expComparison]
  rw [← Category.assoc, ← MonoidalCategory.tensorHom_def]
  rw [inv_prodComparison_natTrans_assoc, ← α.naturality]
  simp only [Category.assoc, Functor.id_obj]

end NaturalTransformation

namespace PrecohesiveMorphism
variable (p : Cohesion.PrecohesiveMorphism E S)
local instance : p.discrete.Full := p.discreteFullyFaithful.full
local instance : p.discrete.Faithful := p.discreteFullyFaithful.faithful
local instance : PreservesFiniteProducts p.pieces := p.piecesPreservesFiniteProducts
local instance : p.points.IsRightAdjoint := p.adjunctions.adj₂.isRightAdjoint

omit [CartesianMonoidalCategory E] [CartesianMonoidalCategory S]
  [MonoidalClosed E] [MonoidalClosed S] in
/-- On a discrete object, points-to-pieces identifies the unit of `Δ ⊣ Γ`
with the inverse counit of `Π ⊣ Δ`. -/
theorem unit_theta (A : S) :
    p.adjunctions.adj₂.unit.app A ≫ (theta p).app (p.discrete.obj A) =
      inv (p.adjunctions.adj₁.counit.app A) := by
  apply IsIso.eq_inv_of_inv_hom_id
  apply p.discrete.map_injective
  simp only [Functor.map_comp, theta,
    Adjunction.Triple.map_rightToLeft_app, Category.assoc]
  dsimp only [Adjunction.Quadruple.leftTriple, Functor.id_obj]
  rw [← Category.assoc, p.adjunctions.adj₂.left_triangle_components]
  simp only [Category.id_comp]
  simp

/-- The canonical map `Γ(X^(Δ A)) → (Γ X)^A`. -/
def pointsExponentialComparison (X : E) (A : S) :
    p.points.obj ((ihom (p.discrete.obj A)).obj X) ⟶
      (ihom A).obj (p.points.obj X) :=
  (expComparison p.points (p.discrete.obj A)).natTrans.app X ≫
    (MonoidalClosed.pre (p.adjunctions.adj₂.unit.app A)).app _

/-- Evaluation compatibility between Continuity and the Nullstellensatz.
The proof only needs the canonical points exponential comparison, and does not
need its stronger property of being an isomorphism. -/
theorem continuity_theta (X : E) (A : S) :
    (theta p).app ((ihom (p.discrete.obj A)).obj X) ≫
      continuityComparison p X A =
    pointsExponentialComparison p X A ≫ (ihom A).map ((theta p).app X) := by
  unfold continuityComparison Cohesion.continuityComparison pointsExponentialComparison
  rw [← unit_theta p A, MonoidalClosed.pre_map]
  simp only [NatTrans.comp_app, Category.assoc]
  rw [expComparison_natTrans_assoc]
  rw [← MonoidalClosed.pre_comm_ihom_map]
  rfl

/-- Epic Continuity and the Nullstellensatz force every power of `θ_X` to
be epic. This is the input to the local-section construction. -/
theorem epi_theta_power (h : EpicContinuity p) (X : E) (A : S) :
    Epi ((ihom A).map ((theta p).app X)) := by
  have := h X A
  have : Epi ((theta p).app ((ihom (p.discrete.obj A)).obj X) ≫
      continuityComparison p X A) := inferInstance
  rw [continuity_theta] at this
  exact epi_of_epi (pointsExponentialComparison p X A) _

end PrecohesiveMorphism
end Cohesion
