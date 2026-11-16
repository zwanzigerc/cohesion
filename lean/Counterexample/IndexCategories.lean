import Counterexample.Groups
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The small indexing categories

Objects are finite product expressions in the three finite groups. Morphisms
are all group homomorphisms between their interpretations. Keeping product
expressions, rather than choosing a skeleton, makes the products explicit.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Counterexample

@[reducible] instance : SmallCategory AbelianWord where
  Hom A B := A.Carrier →* B.Carrier
  id A := MonoidHom.id A.Carrier
  comp f g := g.comp f
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl

/-- These concrete categories keep the entire homomorphism set. -/
instance : ConcreteCategory AbelianWord (fun A B => A.Carrier →* B.Carrier) where
  hom f := f
  ofHom f := f

instance (A B : AbelianWord) : One (A ⟶ B) :=
  inferInstanceAs (One (A.Carrier →* B.Carrier))

@[reducible] instance : SmallCategory GroupWord where
  Hom A B := A.Carrier →* B.Carrier
  id A := MonoidHom.id A.Carrier
  comp f g := g.comp f
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl

instance : ConcreteCategory GroupWord (fun A B => A.Carrier →* B.Carrier) where
  hom f := f
  ofHom f := f

instance (A B : GroupWord) : One (A ⟶ B) :=
  inferInstanceAs (One (A.Carrier →* B.Carrier))

/-- The inclusion is full on all homomorphisms. -/
abbrev inclusion : AbelianWord ⥤ GroupWord where
  obj A := .ab A
  map f := f

instance : inclusion.Full where
  map_surjective f := ⟨f, rfl⟩

instance : inclusion.Faithful where
  map_injective h := h

namespace GroupWord

/-- The map induced on the explicit abelianizations. -/
def reflectMap {B C : GroupWord} (f : B ⟶ C) : B.reflect ⟶ C.reflect :=
  factor ((quotient C).comp f)

@[simp] theorem reflectMap_quotient {B C : GroupWord} (f : B ⟶ C) (x : B.Carrier) :
    reflectMap f (quotient B x) = quotient C (f x) :=
  congrArg (fun h => h x) (factor_comp_quotient ((quotient C).comp f))

end GroupWord

/-- Abelianization on the chosen finite product expressions. -/
abbrev reflector : GroupWord ⥤ AbelianWord where
  obj B := B.reflect
  map f := GroupWord.reflectMap f
  map_id B := by
    apply MonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := B.quotient_surjective x
    change GroupWord.reflectMap (MonoidHom.id B.Carrier) (B.quotient y) = B.quotient y
    exact GroupWord.reflectMap_quotient _ _
  map_comp {X Y Z} f g := by
    apply MonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := GroupWord.quotient_surjective X x
    change GroupWord.reflectMap (g.comp f) (GroupWord.quotient X y) =
      GroupWord.reflectMap g (GroupWord.reflectMap f (GroupWord.quotient X y))
    simp only [GroupWord.reflectMap_quotient]
    rfl

/-- The universal property of abelianization is the reflection adjunction. -/
def reflection : reflector ⊣ inclusion := Adjunction.mkOfHomEquiv
  { homEquiv := fun B A =>
      { toFun := fun f => f.comp (GroupWord.quotient B)
        invFun := fun f => GroupWord.factor f
        left_inv := by
          intro f
          apply MonoidHom.ext
          intro x
          change f (B.quotient (B.sectionHom x)) = f x
          rw [GroupWord.quotient_section]
        right_inv := fun f => GroupWord.factor_comp_quotient f }
    homEquiv_naturality_left_symm := by
      intro B C A f g
      apply MonoidHom.ext
      intro x
      obtain ⟨y, rfl⟩ := B.quotient_surjective x
      change GroupWord.factor (g.comp f) (GroupWord.quotient B y) =
        GroupWord.factor g (GroupWord.reflectMap f (GroupWord.quotient B y))
      rw [GroupWord.reflectMap_quotient]
      exact (congrArg (fun h => h y) (GroupWord.factor_comp_quotient (g.comp f))).trans
        (congrArg (fun h => h (f y)) (GroupWord.factor_comp_quotient g)).symm
    homEquiv_naturality_right := by intros; rfl }

@[simp] theorem reflection_unit (B : GroupWord) :
    reflection.unit.app B = GroupWord.quotient B := by
  rfl

/-- Every unit of the reflection has an actual homomorphic section. -/
theorem reflection_unit_split (B : GroupWord) :
    ∃ s : inclusion.obj (reflector.obj B) ⟶ B, s ≫ reflection.unit.app B = 𝟙 _ := by
  refine ⟨GroupWord.sectionHom B, ?_⟩
  apply MonoidHom.ext
  exact GroupWord.quotient_section B

instance (B : GroupWord) : IsSplitEpi (reflection.unit.app B) where
  exists_splitEpi := by
    obtain ⟨s, hs⟩ := reflection_unit_split B
    exact ⟨⟨s, hs⟩⟩

namespace AbelianWord

def unitIsTerminal : IsTerminal unit :=
  IsTerminal.ofUniqueHom (fun _ => 1) (fun _ _ => by ext)

def productCone (A B : AbelianWord) : BinaryFan A B :=
  BinaryFan.mk (P := A.prod B) (MonoidHom.fst _ _) (MonoidHom.snd _ _)

def productIsLimit (A B : AbelianWord) : IsLimit (productCone A B) := by
  refine BinaryFan.IsLimit.mk _ (fun f g => f.prod g) ?_ ?_ ?_
  · intros; rfl
  · intros; rfl
  · intro T f g m h₁ h₂
    apply MonoidHom.ext
    intro x
    exact Prod.ext (congrArg (fun h => h x) h₁) (congrArg (fun h => h x) h₂)

instance : HasTerminal AbelianWord := unitIsTerminal.hasTerminal

instance (A B : AbelianWord) : HasLimit (pair A B) :=
  HasLimit.mk ⟨productCone A B, productIsLimit A B⟩

instance : HasBinaryProducts AbelianWord := hasBinaryProducts_of_hasLimit_pair AbelianWord

instance : HasFiniteProducts AbelianWord := hasFiniteProducts_of_has_binary_and_terminal

end AbelianWord

namespace GroupWord

def unitIsTerminal : IsTerminal (ab .unit) :=
  IsTerminal.ofUniqueHom (fun _ => 1) (fun _ _ => by ext)

def productCone (A B : GroupWord) : BinaryFan A B :=
  BinaryFan.mk (P := A.prod B) (MonoidHom.fst _ _) (MonoidHom.snd _ _)

def productIsLimit (A B : GroupWord) : IsLimit (productCone A B) := by
  refine BinaryFan.IsLimit.mk _ (fun f g => f.prod g) ?_ ?_ ?_
  · intros; rfl
  · intros; rfl
  · intro T f g m h₁ h₂
    apply MonoidHom.ext
    intro x
    exact Prod.ext (congrArg (fun h => h x) h₁) (congrArg (fun h => h x) h₂)

instance : HasTerminal GroupWord := unitIsTerminal.hasTerminal

instance (A B : GroupWord) : HasLimit (pair A B) :=
  HasLimit.mk ⟨productCone A B, productIsLimit A B⟩

instance : HasBinaryProducts GroupWord := hasBinaryProducts_of_hasLimit_pair GroupWord

instance : HasFiniteProducts GroupWord := hasFiniteProducts_of_has_binary_and_terminal

end GroupWord

@[simp] theorem reflector_map_fst (B C : GroupWord) :
    reflector.map (X := B.prod C) (Y := B) (MonoidHom.fst B.Carrier C.Carrier) =
      (MonoidHom.fst B.reflect.Carrier C.reflect.Carrier : B.reflect.prod C.reflect ⟶
        B.reflect) := by
  apply MonoidHom.ext
  intro x
  exact GroupWord.quotient_section B x.1

@[simp] theorem reflector_map_snd (B C : GroupWord) :
    reflector.map (X := B.prod C) (Y := C) (MonoidHom.snd B.Carrier C.Carrier) =
      (MonoidHom.snd B.reflect.Carrier C.reflect.Carrier : B.reflect.prod C.reflect ⟶
        C.reflect) := by
  apply MonoidHom.ext
  intro x
  exact GroupWord.quotient_section C x.2

instance (B C : GroupWord) : PreservesLimit (pair B C) reflector := by
  apply preservesLimit_of_preserves_limit_cone (GroupWord.productIsLimit B C)
  refine (isLimitMapConeBinaryFanEquiv reflector (P := B.prod C) (X := B) (Y := C)
    (MonoidHom.fst B.Carrier C.Carrier : B.prod C ⟶ B)
    (MonoidHom.snd B.Carrier C.Carrier : B.prod C ⟶ C)).symm ?_
  rw [reflector_map_fst, reflector_map_snd]
  exact AbelianWord.productIsLimit B.reflect C.reflect

instance : PreservesLimitsOfShape (Discrete WalkingPair) reflector where
  preservesLimit {K} :=
    preservesLimit_of_iso_diagram reflector (diagramIsoPair K).symm

instance : PreservesLimit (Functor.empty.{0} GroupWord) reflector := by
  apply preservesLimit_of_preserves_limit_cone GroupWord.unitIsTerminal
  exact (isLimitMapConeEmptyConeEquiv reflector (GroupWord.ab .unit)).symm
    AbelianWord.unitIsTerminal

instance : PreservesLimitsOfShape (Discrete.{0} PEmpty) reflector :=
  preservesLimitsOfShape_pempty_of_preservesTerminal reflector

instance : PreservesFiniteProducts reflector :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal reflector

/-- The inclusion of the alternating subgroup into `S₃`. -/
def kernelInclusion : GroupWord.ab .c3 ⟶ GroupWord.s3 :=
  (alternatingGroup (Fin 3)).subtype

/-- The sign homomorphism, as an arrow of the indexing category. -/
def signMorphism : GroupWord.s3 ⟶ GroupWord.ab .c2 := Equiv.Perm.sign

def unitToC2 : AbelianWord.unit ⟶ AbelianWord.c2 := 1

def kernelToUnit : GroupWord.ab .c3 ⟶ GroupWord.ab .unit := 1

theorem kernelSquare_commutes :
    kernelInclusion ≫ signMorphism = kernelToUnit ≫ inclusion.map unitToC2 := by
  apply MonoidHom.ext
  intro x
  exact x.property

/-- The one pullback needed for the counterexample exists in the small category. -/
theorem kernelSquare_isPullback :
    IsPullback kernelInclusion kernelToUnit signMorphism (inclusion.map unitToC2) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk kernelInclusion kernelToUnit
    kernelSquare_commutes)
  refine PullbackCone.IsLimit.mk kernelSquare_commutes
    (fun s => s.fst.codRestrict (alternatingGroup (Fin 3)) ?_) ?_ ?_ ?_
  · intro x
    have h := congrArg (fun h => h x) s.condition
    exact h
  · intro s
    rfl
  · intro s
    apply MonoidHom.ext
    intro x
    exact Subsingleton.elim _ _
  · intro s m h₁ h₂
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun h => h x) h₁

@[simp] theorem reflector_kernelInclusion : reflector.map kernelInclusion = 1 := by
  apply MonoidHom.ext
  intro x
  exact x.property

/-- Abelianization does not preserve the sign-kernel pullback. -/
theorem kernelSquare_not_preserved :
    ¬ IsPullback (reflector.map kernelInclusion) (reflector.map kernelToUnit)
      (reflector.map signMorphism) (reflector.map (inclusion.map unitToC2)) := by
  intro h
  have heq : (𝟙 AbelianWord.c3) = (1 : AbelianWord.c3 ⟶ AbelianWord.c3) :=
    h.hom_ext (by rw [reflector_kernelInclusion]; rfl)
      (by apply MonoidHom.ext; intro x; exact @Subsingleton.elim PUnit inferInstance _ _)
  have hnontrivial : ∃ x : C3, x ≠ 1 := by decide
  obtain ⟨x, hx⟩ := hnontrivial
  exact hx (congrArg (fun h => h x) heq)

end Counterexample
