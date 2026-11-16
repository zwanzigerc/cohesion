import Cohesion.Cohesive
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# The pointed wedge and the countable-power comparison

Let `p : E → Type` be pre-cohesive, with `E` cartesian closed, complete and
cocomplete. For pointed objects `(X n, x n)` with `Π (X n)` a singleton,
the wedge `A` (all base points identified) satisfies:

* each `X n` is a retract of `A`, and `Π A` is a singleton;
* `A^(Δ ℕ) ≅ ∏ₙ A`, using `Δ ℕ ≅ ∐ₙ 1` and exponentials of coproducts;
* hence `∏ₙ X n` is a retract of `A^(Δ ℕ)`.

Consequently, if `Π (∏ₙ X n)` has two distinct elements, the canonical
comparison `Π (A^(Δ ℕ)) → (Π A)^ℕ` of the cohesion package is not monic.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace RealContinuity

universe u

section ExpCoproduct

variable {E : Type u} [Category.{0} E] [CartesianMonoidalCategory E] [MonoidalClosed E]
  [HasLimits E] [HasColimits E]

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- Exponentials turn coproducts into products. -/
def expSigmaIso {ι : Type} (Z : ι → E) (A : E) :
    (ihom (∐ Z)).obj A ≅ ∏ᶜ fun i => (ihom (Z i)).obj A :=
  (MonoidalClosed.internalHom.flip.obj A).mapIso (opCoproductIsoProduct Z) ≪≫
    PreservesProduct.iso (MonoidalClosed.internalHom.flip.obj A) (fun i => op (Z i))

/-- `A^1 ≅ A`. -/
def expUnitIso (A : E) : (ihom (𝟙_ E)).obj A ≅ A :=
  (MonoidalClosed.unitNatIso.app A).symm

/-- Exponentials along isomorphic objects are isomorphic. -/
def ihomMapIso {W W' : E} (e : W ≅ W') (A : E) : (ihom W').obj A ≅ (ihom W).obj A where
  hom := (MonoidalClosed.pre e.hom).app A
  inv := (MonoidalClosed.pre e.inv).app A
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.inv_hom_id, MonoidalClosed.pre_id]
    rfl
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.hom_inv_id, MonoidalClosed.pre_id]
    rfl

/-- `A^(∐ₙ 1) ≅ ∏ₙ A`. -/
def expSigmaUnitIso (A : E) : (ihom (∐ fun _ : ℕ => 𝟙_ E)).obj A ≅ ∏ᶜ fun _ : ℕ => A :=
  expSigmaIso (fun _ : ℕ => 𝟙_ E) A ≪≫ Pi.mapIso fun _ => expUnitIso A

end ExpCoproduct

section Discrete

variable {E : Type u} [Category.{0} E] [CartesianMonoidalCategory E] [MonoidalClosed E]
  [HasLimits E] [HasColimits E]
variable (p : Cohesion.PrecohesiveMorphism E Type)

/-- `Δ` of the point is terminal. -/
def discretePUnitIso : p.discrete.obj PUnit ≅ 𝟙_ E :=
  haveI := p.discretePreservesFiniteLimits
  IsTerminal.uniqueUpToIso (IsTerminal.isTerminalObj p.discrete PUnit Types.isTerminalPUnit)
    isTerminalTensorUnit

/-- In `Type`, `ℕ` is the coproduct of countably many points. -/
def natIsoSigmaPUnit : (ℕ : Type) ≅ ∐ fun _ : ℕ => PUnit :=
  (Equiv.sigmaPUnit ℕ).symm.toIso ≪≫ (Types.coproductIso fun _ : ℕ => PUnit).symm

/-- `Δ ℕ ≅ ∐ₙ 1`. -/
def discreteNatIso : p.discrete.obj ℕ ≅ ∐ fun _ : ℕ => 𝟙_ E :=
  haveI := p.adjunctions.adj₂.leftAdjoint_preservesColimits
  p.discrete.mapIso (natIsoSigmaPUnit) ≪≫
    PreservesCoproduct.iso p.discrete (fun _ : ℕ => PUnit) ≪≫
    Sigma.mapIso fun _ => discretePUnitIso p

/-- `A^(Δ ℕ) ≅ ∏ₙ A`. -/
def expDiscreteNatIso (A : E) : (ihom (p.discrete.obj ℕ)).obj A ≅ ∏ᶜ fun _ : ℕ => A :=
  (ihomMapIso (discreteNatIso p) A).symm ≪≫ expSigmaUnitIso A

end Discrete

section Wedge

variable {E : Type u} [Category.{0} E] [CartesianMonoidalCategory E] [MonoidalClosed E]
  [HasLimits E] [HasColimits E]
variable (X : ℕ → E) (x : ∀ n, 𝟙_ E ⟶ X n)

/-- The wedge of the pointed objects `(X n, x n)`: the pushout of
`∐ₙ 1 → ∐ₙ X n` (the base points) along `∐ₙ 1 → 1`. -/
abbrev wedge : E := pushout (Limits.Sigma.map x) (toUnit (∐ fun _ : ℕ => 𝟙_ E))

/-- The inclusion of the `n`-th summand into the wedge. -/
def wedgeIncl (n : ℕ) : X n ⟶ wedge X x := Limits.Sigma.ι X n ≫ pushout.inl _ _

/-- The common base point of the wedge. -/
def wedgeBase : 𝟙_ E ⟶ wedge X x := pushout.inr _ _

/-- Components of the retraction onto `X n`: the identity on its own summand,
the constant base point on the others. -/
def wedgeRetrComp (n k : ℕ) : X k ⟶ X n :=
  if h : k = n then eqToHom (congrArg X h) else toUnit (X k) ≫ x n

omit [MonoidalClosed E] [HasLimits E] [HasColimits E] in
theorem wedgeRetrComp_self (n : ℕ) : wedgeRetrComp X x n n = 𝟙 _ := by
  simp [wedgeRetrComp]

omit [MonoidalClosed E] [HasLimits E] [HasColimits E] in
theorem x_wedgeRetrComp (n k : ℕ) : x k ≫ wedgeRetrComp X x n k = x n := by
  unfold wedgeRetrComp
  split_ifs with h
  · subst h; simp
  · rw [← Category.assoc, toUnit_unique (x k ≫ toUnit (X k)) (𝟙 _), Category.id_comp]

/-- The retraction of the wedge onto its `n`-th summand. -/
def wedgeRetr (n : ℕ) : wedge X x ⟶ X n :=
  pushout.desc (Limits.Sigma.desc (wedgeRetrComp X x n)) (x n) (by
    apply Limits.Sigma.hom_ext
    intro k
    rw [Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_comp_desc, x_wedgeRetrComp, ← Category.assoc,
      toUnit_unique (Limits.Sigma.ι _ k ≫ toUnit _) (𝟙 _), Category.id_comp])

omit [MonoidalClosed E] [HasLimits E] in
@[reassoc (attr := simp)]
theorem wedgeIncl_retr (n : ℕ) : wedgeIncl X x n ≫ wedgeRetr X x n = 𝟙 _ := by
  rw [wedgeIncl, wedgeRetr, Category.assoc, pushout.inl_desc, Limits.Sigma.ι_comp_desc,
    wedgeRetrComp_self]

variable (p : Cohesion.PrecohesiveMorphism E Type)

omit [MonoidalClosed E] [HasLimits E] [HasColimits E] in
/-- `Π 1` is a singleton. -/
theorem pieces_unit_unique : Nonempty (Unique (p.pieces.obj (𝟙_ E))) :=
  haveI := p.piecesPreservesFiniteProducts
  ⟨Types.isTerminalEquivUnique _
    (IsTerminal.isTerminalObj p.pieces (𝟙_ E) isTerminalTensorUnit)⟩

omit [MonoidalClosed E] [HasLimits E] in
/-- `Π A` is a singleton for the wedge `A`. -/
theorem subsingleton_pieces_wedge (hX : ∀ n, Subsingleton (p.pieces.obj (X n))) :
    Subsingleton (p.pieces.obj (wedge X x)) := by
  have := p.adjunctions.adj₁.leftAdjoint_preservesColimits
  obtain ⟨hU⟩ := pieces_unit_unique p
  let pt : p.pieces.obj (𝟙_ E) := default
  have hpt : ∀ y : p.pieces.obj (𝟙_ E), y = pt := fun y => Subsingleton.elim _ _
  have key : ∀ a : p.pieces.obj (wedge X x), a = p.pieces.map (wedgeBase X x) pt := by
    intro a
    have hcol := isColimitOfPreserves p.pieces
      (pushoutIsPushout (Limits.Sigma.map x) (toUnit (∐ fun _ : ℕ => 𝟙_ E)))
    obtain ⟨j, y, rfl⟩ := Types.jointly_surjective_of_isColimit hcol a
    rcases j with _ | j
    · -- the apex of the span
      change p.pieces.map (Limits.Sigma.map x ≫ pushout.inl _ _) y = _
      rw [pushout.condition, Functor.map_comp, types_comp_apply, hpt (p.pieces.map _ y)]
      rfl
    · rcases j with _ | _
      · -- the coproduct of the summands
        change p.pieces.map (pushout.inl _ _) y = _
        have hcop := isColimitOfPreserves p.pieces (coproductIsCoproduct X)
        obtain ⟨⟨n⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit hcop y
        change p.pieces.map (pushout.inl _ _) (p.pieces.map (Limits.Sigma.ι X n) z) = _
        have hz : z = p.pieces.map (x n) pt := @Subsingleton.elim _ (hX n) _ _
        rw [hz]
        have e1 : (x n ≫ Limits.Sigma.ι X n) ≫
              pushout.inl (Limits.Sigma.map x) (toUnit (∐ fun _ : ℕ => 𝟙_ E)) =
            (Limits.Sigma.ι (fun _ : ℕ => 𝟙_ E) n ≫ toUnit _) ≫ wedgeBase X x := by
          rw [← Limits.Sigma.ι_map, Category.assoc, pushout.condition, Category.assoc]
          rfl
        calc p.pieces.map (pushout.inl _ _)
              (p.pieces.map (Limits.Sigma.ι X n) (p.pieces.map (x n) pt))
            = p.pieces.map ((x n ≫ Limits.Sigma.ι X n) ≫ pushout.inl _ _) pt := by
              simp only [Functor.map_comp, types_comp_apply]
          _ = p.pieces.map ((Limits.Sigma.ι (fun _ : ℕ => 𝟙_ E) n ≫ toUnit _) ≫
                wedgeBase X x) pt := by rw [e1]
          _ = p.pieces.map (wedgeBase X x)
                (p.pieces.map (Limits.Sigma.ι (fun _ : ℕ => 𝟙_ E) n ≫ toUnit _) pt) := by
              rw [Functor.map_comp, types_comp_apply]
          _ = p.pieces.map (wedgeBase X x) pt := by rw [hpt (p.pieces.map _ pt)]
      · -- the base point
        change p.pieces.map (pushout.inr _ _) y = _
        rw [hpt y]
        rfl
  exact ⟨fun a b => (key a).trans (key b).symm⟩

omit [MonoidalClosed E] [HasLimits E] in
/-- `Π A` is inhabited for the wedge `A`. -/
theorem nonempty_pieces_wedge : Nonempty (p.pieces.obj (wedge X x)) := by
  obtain ⟨hU⟩ := pieces_unit_unique p
  exact ⟨p.pieces.map (wedgeBase X x) default⟩

/-- `∏ₙ X n → A^(Δ ℕ)`, through `∏ₙ A`. -/
def productToPower : (∏ᶜ X) ⟶ (ihom (p.discrete.obj ℕ)).obj (wedge X x) :=
  Limits.Pi.map (wedgeIncl X x) ≫ (expDiscreteNatIso p (wedge X x)).inv

/-- `A^(Δ ℕ) → ∏ₙ X n`, through `∏ₙ A`. -/
def powerToProduct : (ihom (p.discrete.obj ℕ)).obj (wedge X x) ⟶ ∏ᶜ X :=
  (expDiscreteNatIso p (wedge X x)).hom ≫ Limits.Pi.map (wedgeRetr X x)

/-- `∏ₙ X n` is a retract of `A^(Δ ℕ)`. -/
@[reassoc (attr := simp)]
theorem productToPower_powerToProduct :
    productToPower X x p ≫ powerToProduct X x p = 𝟙 _ := by
  simp only [productToPower, powerToProduct, Category.assoc, Iso.inv_hom_id_assoc,
    Limits.Pi.map_comp_map, wedgeIncl_retr]
  exact Limits.Pi.hom_ext _ _ fun n => by simp

/-- Exponentials of types into a subsingleton are subsingletons. -/
theorem subsingleton_ihom_types (A B : Type) [Subsingleton B] :
    Subsingleton ((ihom A).obj B) := by
  constructor
  intro z₁ z₂
  let f₁ : PUnit ⟶ (ihom A).obj B := ↾fun _ => z₁
  let f₂ : PUnit ⟶ (ihom A).obj B := ↾fun _ => z₂
  have h : f₁ = f₂ := MonoidalClosed.uncurry_injective (by ext; exact Subsingleton.elim _ _)
  exact ConcreteCategory.congr_hom h PUnit.unit

/-- **Connected-power criterion.** If each `Π (X n)` is a singleton and
`Π (∏ₙ X n)` has two distinct elements, then the canonical countable-power
comparison of the cohesion package is not monic at the wedge. -/
theorem not_mono_continuityComparison_wedge (hX : ∀ n, Subsingleton (p.pieces.obj (X n)))
    {e₁ e₂ : p.pieces.obj (∏ᶜ X)} (hne : e₁ ≠ e₂) :
    ¬ Mono (p.continuityComparison (wedge X x) ℕ) := by
  intro hmono
  have := subsingleton_pieces_wedge X x p hX
  have := subsingleton_ihom_types ℕ (p.pieces.obj (wedge X x))
  have hinj := (mono_iff_injective _).mp hmono
  have hji : ∀ e, p.pieces.map (powerToProduct X x p) (p.pieces.map (productToPower X x p) e) = e := by
    intro e
    rw [← types_comp_apply (p.pieces.map _) (p.pieces.map _), ← Functor.map_comp,
      productToPower_powerToProduct, CategoryTheory.Functor.map_id]
    rfl
  have h1 : p.pieces.map (productToPower X x p) e₁ ≠ p.pieces.map (productToPower X x p) e₂ :=
    fun h => hne (by rw [← hji e₁, h, hji e₂])
  exact h1 (hinj (Subsingleton.elim _ _))

end Wedge

end RealContinuity
