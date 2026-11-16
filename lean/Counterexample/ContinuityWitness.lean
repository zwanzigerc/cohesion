import Counterexample.Continuity
import Counterexample.IndexCategories
import Counterexample.PullbackObstruction

/-!
# Failure of monic Continuity

For X = y(S₃) and A = y(C₃), the source of the Continuity comparison,
evaluated at the trivial group, is Hom(C₃,S₃), whereas its target is
Hom(C₃,C₂). The former has distinct elements and the latter is a singleton.
Consequently the actual canonical comparison is not a monomorphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open Precohesion.PresheafReflection

namespace Counterexample

def groupUnitIsInitial : IsInitial (GroupWord.ab .unit) :=
  IsInitial.ofUniqueHom (fun _ => 1) (fun _ f => by ext x; cases x; exact f.map_one)

def abelianUnitIsInitial : IsInitial AbelianWord.unit :=
  IsInitial.ofUniqueHom (fun _ => 1) (fun _ f => by ext x; cases x; exact f.map_one)

abbrev continuitySource : Psh AbelianWord :=
  (pieces reflector).obj ((ihom ((discrete reflector).obj
    (yoneda.obj AbelianWord.c3))).obj (yoneda.obj GroupWord.s3))

abbrev continuityTarget : Psh AbelianWord :=
  (ihom (yoneda.obj AbelianWord.c3)).obj ((pieces reflector).obj (yoneda.obj GroupWord.s3))

/-- The source evaluation is the hom-set from C₃ to S₃. -/
def continuitySourceEquiv :
    continuitySource.obj (op AbelianWord.unit) ≃ (C3 →* S3) :=
  (piecesAtInitialEquiv reflector (GroupWord.ab .unit)
    groupUnitIsInitial abelianUnitIsInitial _).trans
    ((exponentialAtTerminalEquiv _ GroupWord.unitIsTerminal _ _).trans
      ((Iso.homCongr (reflection.compYonedaIso.app AbelianWord.c3).symm (Iso.refl _)).trans
        yonedaEquiv))

/-- The target evaluation is the hom-set from C₃ to C₂. -/
def continuityTargetEquiv :
    continuityTarget.obj (op AbelianWord.unit) ≃ (C3 →* C2) :=
  (exponentialAtTerminalEquiv _ AbelianWord.unitIsTerminal _ _).trans
    ((Iso.homCongr (Iso.refl _) ((yonedaPiecesIso reflector).app GroupWord.s3)).trans
      yonedaEquiv)

theorem continuitySource_not_subsingleton :
    ¬ Subsingleton (continuitySource.obj (op AbelianWord.unit)) := by
  intro h
  let := h
  have heq : (alternatingGroup (Fin 3)).subtype = (1 : C3 →* S3) :=
    continuitySourceEquiv.symm.injective (Subsingleton.elim _ _)
  obtain ⟨x, hx⟩ : ∃ x : C3, x ≠ 1 := by decide
  apply hx
  apply Subtype.ext
  exact congrArg (fun f => f x) heq

/-- In fact every map between these particular presheaves fails to be monic. -/
theorem continuityWitness_not_mono (f : continuitySource ⟶ continuityTarget) : ¬ Mono f := by
  intro h
  have hm := (NatTrans.mono_iff_mono_app f).mp h (op AbelianWord.unit)
  have hinj := (CategoryTheory.mono_iff_injective (f.app (op AbelianWord.unit))).mp hm
  apply continuitySource_not_subsingleton
  exact ⟨fun x y => hinj (continuityTargetEquiv.injective (Subsingleton.elim _ _))⟩

/-- The canonical Continuity comparison for y(S₃) and y(C₃) is not monic. -/
theorem canonical_continuity_not_mono :
    ¬ Mono (continuityComparison reflection (yoneda.obj GroupWord.s3)
      (yoneda.obj AbelianWord.c3)) :=
  continuityWitness_not_mono _

end Counterexample
