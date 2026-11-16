import Mathlib.CategoryTheory.Adjunction.Quadruple
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# The adjoint quadruple induced by a reflection

This file constructs the actual Kan extension and restriction functors and
uses mathlib's canonical points-to-pieces natural transformation. A split
reflection unit makes the reflector full. Fullness implies that the unit
of left Kan extension is pointwise surjective, giving the Nullstellensatz.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.ConcreteCategory Opposite

universe u

namespace Precohesion.PresheafReflection

variable {A B : Type u} [SmallCategory A] [SmallCategory B]

/-- The presheaf category on a small category. -/
abbrev Psh (C : Type u) [SmallCategory C] := Cᵒᵖ ⥤ Type u

/-- Left Kan extension along the opposite of the reflector. -/
abbrev pieces (a : B ⥤ A) : Psh B ⥤ Psh A := a.op.lan

/-- Restriction along the opposite of the reflector. -/
abbrev discrete (a : B ⥤ A) : Psh A ⥤ Psh B :=
  (whiskeringLeft Bᵒᵖ Aᵒᵖ (Type u)).obj a.op

/-- Restriction along the opposite of the inclusion. -/
abbrev points (i : A ⥤ B) : Psh B ⥤ Psh A :=
  (whiskeringLeft Aᵒᵖ Bᵒᵖ (Type u)).obj i.op

/-- Right Kan extension along the opposite of the inclusion. -/
abbrev codiscrete (i : A ⥤ B) : Psh A ⥤ Psh B := i.op.ran

variable {a : B ⥤ A} {i : A ⥤ B} (adj : a ⊣ i)

/-- A reflection induces the string Π ⊣ Δ ⊣ Γ ⊣ ∇. -/
def quadruple : Adjunction.Quadruple (pieces a) (discrete a) (points i) (codiscrete i) where
  adj₁ := a.op.lanAdjunction (Type u)
  adj₂ := adj.op.whiskerLeft (Type u)
  adj₃ := i.op.ranAdjunction (Type u)

section FullyFaithful
variable [i.Full] [i.Faithful]

instance middleUnitIso : IsIso (quadruple adj).adj₂.unit := by
  have : ∀ X, IsIso ((quadruple adj).adj₂.unit.app X) := fun X => by
    have : ∀ Y, IsIso (((quadruple adj).adj₂.unit.app X).app Y) := fun Y => by
      change IsIso (X.map ((adj.counit.app Y.unop).op))
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- Restriction along a reflector is fully faithful. -/
def discreteFullyFaithful : (discrete a).FullyFaithful :=
  (quadruple adj).adj₂.fullyFaithfulLOfIsIsoUnit

/-- Restriction is left exact, so Δ is the inverse image of a geometric morphism. -/
instance discretePreservesFiniteLimits : PreservesFiniteLimits (discrete a) := by
  infer_instance

/-- The fourth adjoint is fully faithful as well. -/
def codiscreteFullyFaithful : (codiscrete i).FullyFaithful :=
  (quadruple adj).rightTriple.fullyFaithfulEquiv (discreteFullyFaithful adj)

/-- The canonical comparison Γ ⟶ Π, not an independently chosen map. -/
def theta : points i ⟶ pieces a :=
  letI : (discrete a).Full := (discreteFullyFaithful adj).full
  letI : (discrete a).Faithful := (discreteFullyFaithful adj).faithful
  (quadruple adj).leftTriple.rightToLeft

end FullyFaithful

section KanUnit
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- For a full functor, every element of the pointwise left Kan extension
at an object in its image already comes from that object. -/
theorem lanUnit_app_surjective (L : C ⥤ D) [L.Full] (F : C ⥤ Type u) (X : C) :
    Function.Surjective ((L.lanUnit.app F).app X) := by
  intro x
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (L.obj X)) x
  refine ⟨F.map (L.preimage j.hom) y, ?_⟩
  have hn := congr_hom ((L.lanUnit.app F).naturality (L.preimage j.hom)) y
  change (L.leftKanExtensionUnit F).app X (F.map (L.preimage j.hom) y) =
    (L.leftKanExtension F).map (L.map (L.preimage j.hom))
      ((L.leftKanExtensionUnit F).app j.left y) at hn
  rw [L.map_preimage] at hn
  exact hn.trans hy

/-- Equivalently, the unit of the Kan-extension adjunction is pointwise epic. -/
theorem lanUnit_epi (L : C ⥤ D) [L.Full] (F : C ⥤ Type u) :
    Epi (L.lanUnit.app F) := by
  rw [NatTrans.epi_iff_epi_app]
  intro X
  exact (CategoryTheory.epi_iff_surjective _).2 (lanUnit_app_surjective L F X)

end KanUnit

section Nullstellensatz
variable [i.Full] [i.Faithful]

/-- A full reflector gives the Nullstellensatz for the induced presheaf
quadruple: the canonical comparison from points to pieces is epic. -/
theorem theta_epi_of_full [a.Full] (X : Psh B) : Epi ((theta adj).app X) := by
  let : (discrete a).Full := (discreteFullyFaithful adj).full
  let : (discrete a).Faithful := (discreteFullyFaithful adj).faithful
  change Epi ((quadruple adj).leftTriple.rightToLeft.app X)
  rw [(quadruple adj).leftTriple.epi_rightToLeft_app_iff_epi_map_adj₁_unit_app]
  rw [NatTrans.epi_iff_epi_app]
  intro Y
  change Epi (((a.op.lanAdjunction (Type u)).unit.app X).app (i.op.obj Y))
  rw [Functor.lanAdjunction_unit]
  exact (CategoryTheory.epi_iff_surjective _).2 (lanUnit_app_surjective a.op X (i.op.obj Y))

/-- Menni's sufficient split-unit criterion, proved for the actual canonical
comparison of the actual Kan-extension quadruple. -/
theorem theta_epi_of_split_units [∀ G, IsSplitEpi (adj.unit.app G)] (X : Psh B) :
    Epi ((theta adj).app X) := by
  let : a.Full := adj.full_L_of_isSplitEpi_unit_app
  exact theta_epi_of_full adj X

end Nullstellensatz

end Precohesion.PresheafReflection
