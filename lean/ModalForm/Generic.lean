import Cohesion.Cohesive
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# The modalities `ʃ`, `♭`, `♯` of a pre-cohesive morphism, and continuity stated with `ʃ`

Shulman's real-cohesive type theory states its axioms with three modalities on the topos `E`
itself, not with the adjoints `Π ⊣ Δ ⊣ Γ ⊣ ∇` between `E` and the base:

* the shape `ʃ = ΔΠ`, a monad, with unit `η : X ⟶ ʃX` (`shape`, `shapeUnit`);
* the flat modality `♭ = ΔΓ`, a comonad, with counit `♭X ⟶ X` (`flat`, `flatCounit`);
* the sharp modality `♯ = ∇Γ`, a monad, with unit `X ⟶ ♯X` (`sharp`, `sharpUnit`).

They are the idempotent monads and comonad of the adjunctions `Π ⊣ Δ`, `Δ ⊣ Γ`, `Γ ⊣ ∇`
(`shapeMonad`, `flatComonad`, `sharpMonad`, and `isIso_shapeMonad_μ` etc.), `ʃ ⊣ ♭ ⊣ ♯`
(`shapeFlatAdj`, `flatSharpAdj`), and `♯` is lex (`sharp_preservesFiniteLimits`).

In a (1,1) model, `ʃ = ΔΠ` is the shape of the ordinary topos `E`: on sets it is the
0-truncation `‖ʃ‖₀` of the shape of the corresponding higher model (∞-sheaves on the same site).
Statements about `ʃ` here are therefore the 0-truncated forms of Shulman's.

An object is **discrete** when `♭X ⟶ X` is an isomorphism (`IsDiscrete`), equivalently when
`X ⟶ ʃX` is an isomorphism (`isDiscrete_iff_isIso_shapeUnit`), equivalently when `X ≅ ΔK` for some
`K` (`isDiscrete_iff_exists_iso`).

**Crisp elements.** A lift `♭A ⟶ C` of the counit `♭A ⟶ A` through `c : C ⟶ A` transposes, under
`Δ ⊣ Γ`, to a section of `Γc : ΓC ⟶ ΓA`: a choice of a crisp element of `C` over each crisp
element of `A` (`flat_lift_transpose`).

**The Nullstellensatz, in modal form** (Shulman's Theorem 10.1): `♭X ⟶ X ⟶ ʃX` is an epimorphism
(`epi_flatCounit_shapeUnit`). It is `Δ` of the package's `θ : Γ ⟶ Π`.

**Continuity, stated with `ʃ`.** For an object `X` and a discrete object `Y`, the canonical map
`ʃ(X^Y) ⟶ (ʃX)^Y` is the unique map `c` with `η ≫ c = (η_X)^Y`; it exists because `(ʃX)^Y` is
discrete (`shapeComparison`, `shapeUnit_comp_shapeComparison`, `shapeComparison_unique`). Shulman's
continuity says that it is an equivalence for all crisp sets `X` and crisp discrete sets `Y`;
`ShapeContinuity` says that it is an isomorphism for all `X` and all discrete `Y`. With
`ʃ = ΔΠ` this is the 0-truncated form of Shulman's continuity, which is Lawvere's.

For `Y = ΔA` this map is `Δ` of Lawvere's comparison `κ : Π(X^(ΔA)) ⟶ (ΠX)^A` of the cohesion
package, followed by the isomorphism `Δ(B^A) ≅ (ΔB)^(ΔA)` (`shapeComparison_discrete`). Hence it is
an isomorphism, or a monomorphism, exactly when `κ` is (`isIso_shapeComparison_discrete_iff`,
`mono_shapeComparison_discrete_iff`), and `ShapeContinuity` is equivalent to the package's
`Continuity` (`shapeContinuity_iff`).
-/
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

namespace ModalForm

universe v u₁ u₂

section Modalities

variable {E : Type u₁} {S : Type u₂} [Category.{v} E] [Category.{v} S]
variable (p : Cohesion.PrecohesiveMorphism E S)

/-! ### The modalities -/

/-- **Shape** `ʃ = ΔΠ`. -/
abbrev shape : E ⥤ E := p.pieces ⋙ p.discrete

/-- The unit `X ⟶ ʃX`. -/
abbrev shapeUnit : 𝟭 E ⟶ shape p := p.adjunctions.adj₁.unit

/-- **Flat** `♭ = ΔΓ`. -/
abbrev flat : E ⥤ E := p.points ⋙ p.discrete

/-- The counit `♭X ⟶ X`. -/
abbrev flatCounit : flat p ⟶ 𝟭 E := p.adjunctions.adj₂.counit

/-- **Sharp** `♯ = ∇Γ`. -/
abbrev sharp : E ⥤ E := p.points ⋙ p.codiscrete

/-- The unit `X ⟶ ♯X`. -/
abbrev sharpUnit : 𝟭 E ⟶ sharp p := p.adjunctions.adj₃.unit

/-- A **discrete** object: `♭X ⟶ X` is an isomorphism. -/
def IsDiscrete (X : E) : Prop := IsIso ((flatCounit p).app X)

instance discrete_full : p.discrete.Full := p.discreteFullyFaithful.full
instance discrete_faithful : p.discrete.Faithful := p.discreteFullyFaithful.faithful
instance discrete_isRightAdjoint : p.discrete.IsRightAdjoint := p.adjunctions.adj₁.isRightAdjoint
instance discrete_isLeftAdjoint : p.discrete.IsLeftAdjoint := p.adjunctions.adj₂.isLeftAdjoint

/-- `Δ` is reflective, with reflector `Π`. -/
abbrev discreteReflective : Reflective p.discrete where
  L := p.pieces
  adj := p.adjunctions.adj₁

instance codiscrete_full : p.codiscrete.Full := p.codiscreteFullyFaithful.full
instance codiscrete_faithful : p.codiscrete.Faithful := p.codiscreteFullyFaithful.faithful

/-! ### The modalities as idempotent monads and comonads, with `ʃ ⊣ ♭ ⊣ ♯` -/

/-- `ʃ` as a monad: the monad of `Π ⊣ Δ`. -/
abbrev shapeMonad : Monad E := p.adjunctions.adj₁.toMonad

/-- `♭` as a comonad: the comonad of `Δ ⊣ Γ`. -/
abbrev flatComonad : Comonad E := p.adjunctions.adj₂.toComonad

/-- `♯` as a monad: the monad of `Γ ⊣ ∇`. -/
abbrev sharpMonad : Monad E := p.adjunctions.adj₃.toMonad

theorem shapeMonad_toFunctor : (shapeMonad p).toFunctor = shape p := rfl
theorem shapeMonad_η : (shapeMonad p).η = shapeUnit p := rfl
theorem flatComonad_toFunctor : (flatComonad p).toFunctor = flat p := rfl
theorem flatComonad_ε : (flatComonad p).ε = flatCounit p := rfl
theorem sharpMonad_toFunctor : (sharpMonad p).toFunctor = sharp p := rfl
theorem sharpMonad_η : (sharpMonad p).η = sharpUnit p := rfl

/-- `ʃ` is idempotent: its multiplication `ʃʃ ⟶ ʃ` is invertible. -/
instance isIso_shapeMonad_μ : IsIso (shapeMonad p).μ :=
  inferInstanceAs (IsIso (Functor.whiskerRight
    (Functor.whiskerLeft p.pieces p.adjunctions.adj₁.counit) p.discrete))

/-- `♭` is idempotent: its comultiplication `♭ ⟶ ♭♭` is invertible. -/
instance isIso_flatComonad_δ : IsIso (flatComonad p).δ :=
  inferInstanceAs (IsIso (Functor.whiskerRight
    (Functor.whiskerLeft p.points p.adjunctions.adj₂.unit) p.discrete))

/-- `♯` is idempotent: its multiplication `♯♯ ⟶ ♯` is invertible. -/
instance isIso_sharpMonad_μ : IsIso (sharpMonad p).μ :=
  inferInstanceAs (IsIso (Functor.whiskerRight
    (Functor.whiskerLeft p.points p.adjunctions.adj₃.counit) p.codiscrete))

/-- `ʃ ⊣ ♭` (Shulman's Theorem 9.15, for crisp types). -/
def shapeFlatAdj : shape p ⊣ flat p := p.adjunctions.adj₁.comp p.adjunctions.adj₂

/-- `♭ ⊣ ♯` (Shulman's Corollary 6.26, for crisp types). -/
def flatSharpAdj : flat p ⊣ sharp p := p.adjunctions.adj₃.comp p.adjunctions.adj₂

/-- `♯` is lex: as a right adjoint, of `♭`, it preserves finite limits. -/
instance sharp_preservesFiniteLimits : PreservesFiniteLimits (sharp p) := by
  have := (flatSharpAdj p).rightAdjoint_preservesLimits
  infer_instance

variable {p}

/-! ### Discrete objects -/

theorem isDiscrete_iff_essImage (X : E) : IsDiscrete p X ↔ p.discrete.essImage X :=
  p.adjunctions.adj₂.isIso_counit_app_iff_mem_essImage

theorem isDiscrete_iff_exists_iso (X : E) :
    IsDiscrete p X ↔ ∃ K : S, Nonempty (X ≅ p.discrete.obj K) := by
  rw [isDiscrete_iff_essImage]
  exact ⟨fun ⟨K, ⟨e⟩⟩ => ⟨K, ⟨e.symm⟩⟩, fun ⟨K, ⟨e⟩⟩ => ⟨K, ⟨e.symm⟩⟩⟩

/-- Discrete objects are exactly the `ʃ`-modal ones. -/
theorem isDiscrete_iff_isIso_shapeUnit (X : E) :
    IsDiscrete p X ↔ IsIso ((shapeUnit p).app X) :=
  (isDiscrete_iff_essImage X).trans p.adjunctions.adj₁.isIso_unit_app_iff_mem_essImage.symm

theorem isDiscrete_discrete (A : S) : IsDiscrete p (p.discrete.obj A) :=
  (isDiscrete_iff_essImage _).mpr (p.discrete.obj_mem_essImage A)

theorem isDiscrete_shape (X : E) : IsDiscrete p ((shape p).obj X) :=
  isDiscrete_discrete _

theorem isDiscrete_flat (X : E) : IsDiscrete p ((flat p).obj X) :=
  isDiscrete_discrete _

/-! ### Crisp elements through `♭` -/

/-- A lift `σ : ♭A ⟶ C` of the counit `♭A ⟶ A` through `c : C ⟶ A` transposes, under `Δ ⊣ Γ`, to
a section `ΓA ⟶ ΓC` of `Γc`: a choice of a crisp element of `C` over each crisp element of `A`. -/
theorem flat_lift_transpose {A C : E} (c : C ⟶ A) (σ : (flat p).obj A ⟶ C)
    (hσ : σ ≫ c = (flatCounit p).app A) :
    p.adjunctions.adj₂.homEquiv _ _ σ ≫ p.points.map c = 𝟙 _ := by
  rw [← Adjunction.homEquiv_naturality_right, hσ, Adjunction.homEquiv_unit]
  exact p.adjunctions.adj₂.right_triangle_components A

/-! ### The Nullstellensatz -/

/-- `♭X ⟶ X ⟶ ʃX` is `Δ` of `θ : ΓX ⟶ ΠX`. -/
theorem discrete_map_theta (X : E) :
    p.discrete.map (p.adjunctions.leftTriple.rightToLeft.app X) =
      (flatCounit p).app X ≫ (shapeUnit p).app X :=
  p.adjunctions.leftTriple.map_rightToLeft_app X

/-- **The Nullstellensatz, in modal form**: `♭X ⟶ X ⟶ ʃX` is an epimorphism. -/
theorem epi_flatCounit_shapeUnit (X : E) : Epi ((flatCounit p).app X ≫ (shapeUnit p).app X) := by
  rw [← discrete_map_theta]
  have : Epi (p.adjunctions.leftTriple.rightToLeft.app X) := p.nullstellensatz X
  infer_instance

end Modalities

section Exponentials

variable {E : Type u₁} {S : Type u₂} [Category.{v} E] [Category.{v} S]
  [CartesianMonoidalCategory E] [CartesianMonoidalCategory S]
  [MonoidalClosed E] [MonoidalClosed S]
variable (p : Cohesion.PrecohesiveMorphism E S)

instance pieces_preservesFiniteProducts : PreservesFiniteProducts p.pieces :=
  p.piecesPreservesFiniteProducts

/-- `Δ` preserves exponentials (Frobenius reciprocity, since `Π` preserves binary products). -/
instance discrete_monoidalClosed : MonoidalClosedFunctor p.discrete :=
  cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts p.discrete p.adjunctions.adj₁

variable {p}

omit [CartesianMonoidalCategory E] in
/-- Precomposition with an isomorphism of exponents. -/
def preIso {A B : E} (e : A ≅ B) (Z : E) : (ihom B).obj Z ≅ (ihom A).obj Z where
  hom := (pre e.hom).app Z
  inv := (pre e.inv).app Z
  hom_inv_id := by rw [← NatTrans.comp_app, ← pre_map, e.inv_hom_id, pre_id]; rfl
  inv_hom_id := by rw [← NatTrans.comp_app, ← pre_map, e.hom_inv_id, pre_id]; rfl

/-- **Exponentials of discrete objects are discrete.** -/
theorem isDiscrete_ihom {Y Z : E} (hY : IsDiscrete p Y) (hZ : IsDiscrete p Z) :
    IsDiscrete p ((ihom Y).obj Z) := by
  rw [isDiscrete_iff_essImage] at *
  obtain ⟨A, ⟨eA⟩⟩ := hY
  obtain ⟨B, ⟨eB⟩⟩ := hZ
  exact ⟨(ihom A).obj B, ⟨asIso ((expComparison p.discrete A).natTrans.app B) ≪≫
    (ihom (p.discrete.obj A)).mapIso eB ≪≫ preIso eA.symm Z⟩⟩

/-! ### The canonical map `ʃ(X^Y) ⟶ (ʃX)^Y` -/

theorem essImage_ihom_shape (X : E) {Y : E} (hY : IsDiscrete p Y) :
    p.discrete.essImage ((ihom Y).obj ((shape p).obj X)) :=
  (isDiscrete_iff_essImage _).mp (isDiscrete_ihom hY (isDiscrete_shape X))

/-- **The canonical map `ʃ(X^Y) ⟶ (ʃX)^Y`**, for a discrete `Y`: the unique map `c` with
`η ≫ c = (η_X)^Y`. -/
def shapeComparison (X : E) {Y : E} (hY : IsDiscrete p Y) :
    (shape p).obj ((ihom Y).obj X) ⟶ (ihom Y).obj ((shape p).obj X) :=
  letI := discreteReflective p
  unitCompPartialBijective ((ihom Y).obj X) (essImage_ihom_shape X hY)
    ((ihom Y).map ((shapeUnit p).app X))

/-- `η ≫ c = (η_X)^Y`. -/
@[reassoc]
theorem shapeUnit_comp_shapeComparison (X : E) {Y : E} (hY : IsDiscrete p Y) :
    (shapeUnit p).app ((ihom Y).obj X) ≫ shapeComparison X hY =
      (ihom Y).map ((shapeUnit p).app X) := by
  let _ := discreteReflective p
  have h := unitCompPartialBijective_symm_apply (i := p.discrete) ((ihom Y).obj X)
    (essImage_ihom_shape X hY) (shapeComparison X hY)
  rw [shapeComparison, Equiv.symm_apply_apply] at h
  exact h.symm

/-- **Uniqueness**: any `c` with `η ≫ c = (η_X)^Y` is the canonical map. -/
theorem shapeComparison_unique (X : E) {Y : E} (hY : IsDiscrete p Y)
    (c : (shape p).obj ((ihom Y).obj X) ⟶ (ihom Y).obj ((shape p).obj X))
    (hc : (shapeUnit p).app ((ihom Y).obj X) ≫ c = (ihom Y).map ((shapeUnit p).app X)) :
    c = shapeComparison X hY := by
  let _ := discreteReflective p
  have h := unitCompPartialBijective_symm_apply (i := p.discrete) ((ihom Y).obj X)
    (essImage_ihom_shape X hY) c
  have h' : (unitCompPartialBijective (i := p.discrete) ((ihom Y).obj X)
      (essImage_ihom_shape X hY)).symm c = (ihom Y).map ((shapeUnit p).app X) := h.trans hc
  exact (Equiv.symm_apply_eq _).mp h'

/-- The canonical maps for isomorphic discrete exponents are conjugate. -/
theorem shapeComparison_conj (X : E) {Y Y' : E} (hY : IsDiscrete p Y) (hY' : IsDiscrete p Y')
    (e : Y ≅ Y') :
    shapeComparison X hY' = (shape p).map ((pre e.hom).app X) ≫ shapeComparison X hY ≫
      (pre e.inv).app ((shape p).obj X) := by
  refine (shapeComparison_unique X hY' _ ?_).symm
  have h1 := (shapeUnit p).naturality ((pre e.hom).app X)
  simp only [Functor.id_map] at h1
  rw [← Category.assoc, ← h1, Category.assoc, shapeUnit_comp_shapeComparison_assoc]
  rw [show (ihom Y).map ((shapeUnit p).app X) ≫ (pre e.inv).app ((shape p).obj X) =
      (pre e.inv).app X ≫ (ihom Y').map ((shapeUnit p).app X) from
    (pre_comm_ihom_map e.inv _).symm]
  rw [← Category.assoc, ← NatTrans.comp_app, ← pre_map, e.inv_hom_id, pre_id, NatTrans.id_app]
  exact Category.id_comp _

theorem isIso_shapeComparison_iff_of_iso (X : E) {Y Y' : E} (hY : IsDiscrete p Y)
    (hY' : IsDiscrete p Y') (e : Y ≅ Y') :
    IsIso (shapeComparison X hY') ↔ IsIso (shapeComparison X hY) := by
  rw [shapeComparison_conj X hY hY' e]
  have : IsIso ((pre e.hom).app X) := inferInstanceAs (IsIso (preIso e X).hom)
  have : IsIso ((pre e.inv).app ((shape p).obj X)) :=
    inferInstanceAs (IsIso (preIso e ((shape p).obj X)).inv)
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

/-! ### Comparison with Lawvere's continuity -/

omit [MonoidalClosed E] [MonoidalClosed S] in
/-- `Δ` of the projections is jointly monic. -/
theorem discrete_hom_ext {Z : E} {B C : S} {f g : Z ⟶ p.discrete.obj (B ⊗ C)}
    (h₁ : f ≫ p.discrete.map (fst B C) = g ≫ p.discrete.map (fst B C))
    (h₂ : f ≫ p.discrete.map (snd B C) = g ≫ p.discrete.map (snd B C)) : f = g := by
  rw [← cancel_mono (CartesianMonoidalCategory.prodComparison p.discrete B C)]
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst] using h₁
  · simpa only [Category.assoc, CartesianMonoidalCategory.prodComparison_snd] using h₂

omit [MonoidalClosed E] [MonoidalClosed S] in
/-- The unit of `Π ⊣ Δ` at a product `ΔA ⊗ W`, through `ΠΔA ≅ A`. -/
theorem unit_tensor (A : S) (W : E) :
    (p.discrete.obj A ◁ (shapeUnit p).app W) ≫
      inv (CartesianMonoidalCategory.prodComparison p.discrete A (p.pieces.obj W)) ≫
        p.discrete.map (inv (p.adjunctions.adj₁.counit.app A) ▷ p.pieces.obj W) ≫
          p.discrete.map
            (inv (CartesianMonoidalCategory.prodComparison p.pieces (p.discrete.obj A) W)) =
      (shapeUnit p).app (p.discrete.obj A ⊗ W) := by
  rw [Functor.map_inv]
  simp only [← Category.assoc]
  rw [IsIso.comp_inv_eq]
  have hη : p.discrete.map (inv (p.adjunctions.adj₁.counit.app A)) =
      (shapeUnit p).app (p.discrete.obj A) := by
    rw [Functor.map_inv]
    exact IsIso.inv_eq_of_inv_hom_id (p.adjunctions.adj₁.right_triangle_components A)
  apply discrete_hom_ext
  · simp only [Category.assoc, ← Functor.map_comp, CartesianMonoidalCategory.whiskerRight_fst,
      CartesianMonoidalCategory.prodComparison_fst, Functor.id_obj, Functor.comp_obj]
    rw [Functor.map_comp, CartesianMonoidalCategory.inv_prodComparison_map_fst_assoc,
      CartesianMonoidalCategory.whiskerLeft_fst_assoc, hη]
    exact (shapeUnit p).naturality _
  · simp only [Category.assoc, ← Functor.map_comp, CartesianMonoidalCategory.whiskerRight_snd,
      CartesianMonoidalCategory.prodComparison_snd, Functor.id_obj, Functor.comp_obj]
    rw [CartesianMonoidalCategory.inv_prodComparison_map_snd,
      CartesianMonoidalCategory.whiskerLeft_snd]
    exact (shapeUnit p).naturality _

/-- **The canonical map for `Y = ΔA` satisfies the defining equation with `Δκ`.** -/
theorem shapeUnit_comp_discrete_map_continuityComparison (X : E) (A : S) :
    (shapeUnit p).app ((ihom (p.discrete.obj A)).obj X) ≫
        p.discrete.map (p.continuityComparison X A) ≫
          (expComparison p.discrete A).natTrans.app (p.pieces.obj X) =
      (ihom (p.discrete.obj A)).map ((shapeUnit p).app X) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_expComparison,
    ← CartesianMonoidalCategory.prodComparison_inv_natural_whiskerLeft_assoc,
    ← Functor.map_comp, ← uncurry_eq]
  rw [← Category.id_comp ((ihom (p.discrete.obj A)).map ((shapeUnit p).app X)),
    uncurry_natural_right, uncurry_id_eq_ev]
  simp only [Functor.id_obj]
  have h : (ihom.ev (p.discrete.obj A)).app X ≫ (shapeUnit p).app X =
      (shapeUnit p).app (p.discrete.obj A ⊗ (ihom (p.discrete.obj A)).obj X) ≫
        p.discrete.map (p.pieces.map ((ihom.ev (p.discrete.obj A)).app X)) :=
    (shapeUnit p).naturality _
  rw [h]
  simp only [Cohesion.PrecohesiveMorphism.continuityComparison, Cohesion.continuityComparison]
  rw [uncurry_pre_app, uncurry_expComparison, Functor.map_comp, Functor.map_comp,
    ← unit_tensor A ((ihom (p.discrete.obj A)).obj X)]
  simp only [Category.assoc]

/-- **For `Y = ΔA`, the canonical map is `Δ` of Lawvere's comparison**, followed by
`Δ(B^A) ≅ (ΔB)^(ΔA)`. -/
theorem shapeComparison_discrete (X : E) (A : S) :
    shapeComparison X (isDiscrete_discrete (p := p) A) =
      p.discrete.map (p.continuityComparison X A) ≫
        (expComparison p.discrete A).natTrans.app (p.pieces.obj X) :=
  (shapeComparison_unique X _ _ (shapeUnit_comp_discrete_map_continuityComparison X A)).symm

/-- **The canonical map is an isomorphism exactly when Lawvere's comparison is.** -/
theorem isIso_shapeComparison_discrete_iff (X : E) (A : S) :
    IsIso (shapeComparison X (isDiscrete_discrete (p := p) A)) ↔
      IsIso (p.continuityComparison X A) := by
  rw [shapeComparison_discrete, isIso_comp_right_iff]
  exact ⟨fun _ => isIso_of_fully_faithful p.discrete _, fun _ => inferInstance⟩

/-- **The canonical map is a monomorphism exactly when Lawvere's comparison is.** -/
theorem mono_shapeComparison_discrete_iff (X : E) (A : S) :
    Mono (shapeComparison X (isDiscrete_discrete (p := p) A)) ↔
      Mono (p.continuityComparison X A) := by
  rw [shapeComparison_discrete]
  constructor
  · intro h
    have : Mono (p.discrete.map (p.continuityComparison X A)) := mono_of_mono _
      ((expComparison p.discrete A).natTrans.app (p.pieces.obj X))
    exact p.discrete.mono_of_mono_map this
  · intro h
    infer_instance

variable (p) in
/-- **Continuity, stated with `ʃ`**: for every `X` and every discrete `Y`, the canonical map
`ʃ(X^Y) ⟶ (ʃX)^Y` is an isomorphism. In a (1,1) model, where `ʃ = ΔΠ`, this is the 0-truncated
form of Shulman's continuity. -/
def ShapeContinuity : Prop :=
  ∀ (X Y : E) (hY : IsDiscrete p Y), IsIso (shapeComparison X hY)

/-- **Continuity stated with `ʃ = ΔΠ` is Lawvere's continuity.** -/
theorem shapeContinuity_iff : ShapeContinuity p ↔ p.Continuity := by
  constructor
  · intro h X A
    exact (isIso_shapeComparison_discrete_iff X A).mp (h X _ (isDiscrete_discrete A))
  · intro h X Y hY
    have : IsIso ((flatCounit p).app Y) := hY
    rw [isIso_shapeComparison_iff_of_iso X (isDiscrete_discrete _) hY
      (asIso ((flatCounit p).app Y))]
    exact (isIso_shapeComparison_discrete_iff X _).mpr (h X _)

end Exponentials

end ModalForm
