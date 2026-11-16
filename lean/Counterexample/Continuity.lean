import Cohesion.Continuity
import Counterexample.PresheafReflection
import Counterexample.ProductTransfer
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.HomCongr

/-! # An explicit obstruction to monic Continuity -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.CartesianMonoidalCategory

universe u

namespace Precohesion.PresheafReflection

variable {A B : Type u} [SmallCategory A] [SmallCategory B]

/-- At a common initial object, the pointwise Kan-extension comma category
has the identity arrow as a terminal object. -/
def initialCostructuredTerminal (a : B ⥤ A) (b : B)
    (hb : IsInitial b) (ha : IsInitial (a.obj b)) :
    IsTerminal (CostructuredArrow.mk (𝟙 (a.op.obj (op b)))) := by
  refine IsTerminal.ofUniqueHom (fun X => CostructuredArrow.homMk
    (hb.to X.left.unop).op ?_) ?_
  · apply Quiver.Hom.unop_inj
    exact ha.hom_ext _ _
  · intro X f
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    exact hb.hom_ext _ _

/-- A left Kan extension does not change evaluation at a common initial object. -/
theorem lanUnit_isIso_at_initial (a : B ⥤ A) (b : B)
    (hb : IsInitial b) (ha : IsInitial (a.obj b)) (Z : Psh B) :
    IsIso ((a.op.lanUnit.app Z).app (op b)) := by
  have h := a.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit Z (a.op.obj (op b))
  simpa [Functor.lan, Functor.lanUnit] using
    h.isIso_ι_app_of_isTerminal _ (initialCostructuredTerminal a b hb ha)

/-- The associated bijection of the two evaluation sets. -/
def piecesAtInitialEquiv (a : B ⥤ A) (b : B)
    (hb : IsInitial b) (ha : IsInitial (a.obj b)) (Z : Psh B) :
    ((pieces a).obj Z).obj (op (a.obj b)) ≃ Z.obj (op b) := by
  let : IsIso ((a.op.lanUnit.app Z).app (op b)) := lanUnit_isIso_at_initial a b hb ha Z
  exact (asIso ((a.op.lanUnit.app Z).app (op b))).toEquiv.symm

/-- Evaluation of an exponential at a terminal indexing object is the set
of natural transformations between its base and exponent. -/
def exponentialAtTerminalEquiv (b : B) (hb : IsTerminal b) (D X : Psh B) :
    ((ihom D).obj X).obj (op b) ≃ (D ⟶ X) := by
  let e : yoneda.obj b ≅ 𝟙_ (Psh B) :=
    (hb.isTerminalObj yoneda b).uniqueUpToIso isTerminalTensorUnit
  exact yonedaEquiv.symm.trans
    (((ihom.adjunction D).homEquiv (yoneda.obj b) X).symm.trans
      (Iso.homCongr ((tensorIso (Iso.refl D) e) ≪≫ ρ_ D) (Iso.refl X)))

/-- The canonical Continuity comparison: the exponential comparison for Π,
followed by the identification ΠΔA ≅ A supplied by the counit. -/
def continuityComparison {a : B ⥤ A} {i : A ⥤ B} (adj : a ⊣ i)
    [i.Full] [i.Faithful] [HasFiniteProducts B] [PreservesFiniteProducts a]
    (X : Psh B) (D : Psh A) :
    (pieces a).obj ((ihom ((discrete a).obj D)).obj X) ⟶
      (ihom D).obj ((pieces a).obj X) := by
  let : PreservesFiniteProducts (pieces a) := preservesFiniteProducts_lan_op a
  let : (discrete a).Full := (discreteFullyFaithful adj).full
  let : (discrete a).Faithful := (discreteFullyFaithful adj).faithful
  exact Cohesion.continuityComparison (quadruple adj).adj₁ X D

end Precohesion.PresheafReflection
