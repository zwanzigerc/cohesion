{-# OPTIONS --cohesion --without-K --flat-split #-}

-- THE IDENTITY LAWS of the canonical comparisons, as named exports.
-- Claude (Fable), 13 November 2026; after fable-impl-17 (HANDOFF-34 item 1;
-- REFLECTION-ISSUES R31; REINDEXING-IDENTITY-EXPORT-READINESS-01, whose
-- sections 3 to 5 this follows). Postulate-free; no reflection; it declares
-- nothing. Composition (ReindexingComposition), naturality in the choices
-- (ReindexingChoice) and the assembly are not touched and not proved again.
--
-- DATA, all crisp: a level ℓ; Γ : Set ℓ with dΓ : Discrete Γ; A : Γ → Set ℓ;
-- relative reflections K, L (and M) of A over Γ. Γ may be a HIGHER discrete
-- type: no statement here asks Γ to be a set. Only the fibres of the
-- reflections are sets, as RelativeShapeOver requires.
--
-- 1. SelfChoice.factor-unit K          NO extensionality
--      the factorisation of the unit of K through K itself is id-over.
--    ChoiceIdentity fe K               (fe only names the Choice modules)
--      choice-id-over    Choice.forward-over fe K K ≡ id-over
--      choice-id         forward z ≡ z
--      fibre-choice-id   FiberChoice.forward fe K K γ w ≡ w
--
-- 2. ChoiceComposition fe K L M        uses fe
--      choice-compose-over   forward-over K M ≡ forward-over L M ∘ K L
--      choice-compose, fibre-choice-compose   the same pointwise
--    Not asked for by the handoff; the readiness note recommends it with
--    the identity, and it is ten lines by the uniqueness half of K.
--
-- 3. IdentityComparison fe Γ dΓ A K L  uses fe
--    I = ShapeReindexing.Comparison Γ Γ dΓ dΓ A id K L: the canonical
--    comparison along the IDENTITY of Γ, from the reflection L (in the
--    place of the reflection after substitution) to K.
--      comparison-is-fibre-map   I.comparison γ w ≡ fiber-map m γ w, where
--                                m is I.comparison-over followed by the
--                                forgetful map of the identity pullback.
--                                Path algebra; NO extensionality.
--      identity-choice           I.comparison γ w ≡ FiberChoice.forward
--                                fe L K γ w: along id the reindexing
--                                comparison IS the comparison of the two
--                                choices, at every point of every fibre.
--      identity-comparison-is-equivalence   I.ComparisonIsEquivalence,
--                                from the inverse that FiberChoice has.
--                                For f = id ONLY.
--
-- 4. IdentityLaw fe Γ dΓ A K           uses fe
--    I = ShapeReindexing.Comparison Γ Γ dΓ dΓ A id K K.
--      identity-fibre   I.comparison γ w ≡ w
--      identity-total   I.comparison-total z ≡ (projection K z , (z , refl))
--
-- EQUALITY STRENGTH. Every statement about a comparison is an equality of
-- VALUES at each point: of points of a fibre (3, 4) or of the identity
-- pullback (identity-total). None is an equality of functions, and none
-- says that a comparison is judgmentally the identity: Output.factor is
-- the inverse of an equivalence and has propositional laws only. The two
-- -over statements of 1 and 2 are equalities of whole MapOver records,
-- triangles included, as ShapeChoice states its own laws.
-- comparison-total along id does not have the type Total K → Total K: its
-- codomain is the pullback of the projection along id, and identity-total
-- says which point of it is hit, without identifying that pullback with
-- Total K.
--
-- EXTENSIONALITY. fe : FunExtAt ℓ, crisp, the hypothesis ShapeChoice has.
-- It is used in 2 and 3 through the algebra of MapOver (compose-assoc, and
-- once directly on the triangles of a unit). The proof of 1 does not use
-- it. Nothing is assumed about stability, and no comparison along a map
-- other than the identity becomes an equivalence.
module ReindexingIdentity where

open import Foundations
open import RelativeSliceShape
import ShapeChoice
open ShapeChoice
  using (FunExtAt; id-over; compose-over; fiber-map; fiber-map-id;
         fiber-map-compose; assoc)
open import FlatContext using (right-unit)
open import PullbackSetFibers using (transport)
open import Adjointify using (quasi-inverse)
open import ShapeReindexing using (module Comparison)

------------------------------------------------------------------------
-- 1. One choice compared with itself.

module SelfChoice
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} {@♭ A : Γ → Set ℓ}
  (@♭ K : RelativeShapeOver Γ dΓ A) where

  private
    unit-K : MapOver (fst {B = A}) (Output.projection K)
    unit-K = over-map (Output.unit K) (Output.unit-over K)

  -- No extensionality: the η law of the universal property at id-over.
  factor-unit : Output.factor K (Output.Total K) (Output.total-discrete K)
                  (Output.projection K) (Output.family-set K) unit-K
                ≡ id-over (Output.projection K)
  factor-unit = ShapeChoice.Uniqueness.factor-η K (Output.Total K)
    (Output.total-discrete K) (Output.projection K) (Output.family-set K)
    (id-over (Output.projection K))

module ChoiceIdentity
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} {@♭ A : Γ → Set ℓ}
  (@♭ K : RelativeShapeOver Γ dΓ A) where

  private
    module C = ShapeChoice.Choice fe K K
    module F = ShapeChoice.FiberChoice fe K K

  choice-id-over : C.forward-over ≡ id-over (Output.projection K)
  choice-id-over = SelfChoice.factor-unit K

  choice-id : (z : Output.Total K) → C.forward z ≡ z
  choice-id z = ap (λ m → function m z) choice-id-over

  fibre-choice-id : (γ : Γ) (w : Output.family K γ) → F.forward γ w ≡ w
  fibre-choice-id γ w = ap (λ m → fiber-map m γ w) choice-id-over
                      ∙ fiber-map-id γ w

------------------------------------------------------------------------
-- 2. Three choices.

module ChoiceComposition
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} {@♭ A : Γ → Set ℓ}
  (@♭ K L M : RelativeShapeOver Γ dΓ A) where

  private
    module KL = ShapeChoice.Choice fe K L
    module LM = ShapeChoice.Choice fe L M
    module KM = ShapeChoice.Choice fe K M
    module FKL = ShapeChoice.FiberChoice fe K L
    module FLM = ShapeChoice.FiberChoice fe L M
    module FKM = ShapeChoice.FiberChoice fe K M
    open ShapeChoice.Algebra fe using (compose-assoc)

  choice-compose-over :
    KM.forward-over ≡ compose-over LM.forward-over KL.forward-over
  choice-compose-over = sym (KM.forward-unique
    (compose-over LM.forward-over KL.forward-over)
    ( compose-assoc LM.forward-over KL.forward-over KL.unit-s
    ∙ ap (compose-over LM.forward-over) KL.forward-unit
    ∙ LM.forward-unit ))

  choice-compose : (z : Output.Total K)
                 → KM.forward z ≡ LM.forward (KL.forward z)
  choice-compose z = ap (λ m → function m z) choice-compose-over

  fibre-choice-compose : (γ : Γ) (w : Output.family K γ)
                       → FKM.forward γ w ≡ FLM.forward γ (FKL.forward γ w)
  fibre-choice-compose γ w =
    ap (λ m → fiber-map m γ w) choice-compose-over
    ∙ sym (fiber-map-compose LM.forward-over KL.forward-over γ w)

------------------------------------------------------------------------
-- 3. The comparison along the identity of the base, for two choices.

module IdentityComparison
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  (@♭ Γ : Set ℓ) (@♭ dΓ : Discrete Γ) (@♭ A : Γ → Set ℓ)
  (@♭ K L : RelativeShapeOver Γ dΓ A) where

  -- A ∘ id is A, so L is a reflection of the substituted family.
  module I = Comparison Γ Γ dΓ dΓ A id K L
  module C = ShapeChoice.Choice fe L K
  module F = ShapeChoice.FiberChoice fe L K

  private
    open ShapeChoice.Algebra fe using (compose-assoc)

    pK : Output.Total K → Γ
    pK = Output.projection K

    -- From the pullback of pK along id back to the total space of K, over Γ.
    forget-over : MapOver I.pulled-projection pK
    forget-over = over-map (λ w → fst (snd w)) (λ w → snd (snd w))

    m : MapOver (Output.projection L) pK
    m = compose-over forget-over I.comparison-over

    -- The function is the unit of K on the nose; the triangles differ by
    -- a right unit. The one direct use of extensionality.
    forget-unit : compose-over forget-over I.pulled-unit ≡ C.unit-t
    forget-unit = ap (over-map {p = fst {B = A}} {q = pK} (Output.unit K))
      (fe (λ a → right-unit (Output.unit-over K a)))

    m-unit : compose-over m C.unit-s ≡ C.unit-t
    m-unit =
      compose-assoc forget-over I.comparison-over C.unit-s
      ∙ ap (compose-over forget-over)
          (Output.factor-β L I.PulledTotal I.pulled-discrete
             I.pulled-projection I.pulled-set-fibers I.pulled-unit)
      ∙ forget-unit

    m-is-choice : m ≡ C.forward-over
    m-is-choice = C.forward-unique m m-unit

    transport-fibre : {δ γ : Γ} (s : δ ≡ γ)
                    → (y : Output.Total K) (q : pK y ≡ δ)
                    → transport (λ γ′ → Fiber pK γ′) s (y , q) ≡ (y , q ∙ s)
    transport-fibre refl y q = ap (λ r → y , r) (sym (right-unit q))

  -- Path algebra only: the fibre form of the comparison is the map that
  -- its total form induces on fibres.
  comparison-is-fibre-map : (γ : Γ) (w : Output.family L γ)
                          → I.comparison γ w ≡ fiber-map m γ w
  comparison-is-fibre-map γ (z , e) =
    transport-fibre (triangle I.comparison-over z ∙ e)
      (fst (snd (I.comparison-total z))) (snd (snd (I.comparison-total z)))
    ∙ ap (λ r → fst (snd (I.comparison-total z)) , r)
        (sym (assoc (snd (snd (I.comparison-total z)))
                    (triangle I.comparison-over z) e))

  identity-choice : (γ : Γ) (w : Output.family L γ)
                  → I.comparison γ w ≡ F.forward γ w
  identity-choice γ w = comparison-is-fibre-map γ w
                      ∙ ap (λ n → fiber-map n γ w) m-is-choice

  -- Hence the comparison along the identity is an equivalence. This is
  -- about f = id; it says nothing for any other map.
  identity-comparison-is-equivalence : I.ComparisonIsEquivalence
  identity-comparison-is-equivalence γ = quasi-inverse (F.backward γ)
    (λ y → identity-choice γ (F.backward γ y) ∙ F.forward-backward γ y)
    (λ w → ap (F.backward γ) (identity-choice γ w) ∙ F.backward-forward γ w)

------------------------------------------------------------------------
-- 4. The comparison along the identity, for one choice.

module IdentityLaw
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  (@♭ Γ : Set ℓ) (@♭ dΓ : Discrete Γ) (@♭ A : Γ → Set ℓ)
  (@♭ K : RelativeShapeOver Γ dΓ A) where

  module I = Comparison Γ Γ dΓ dΓ A id K K

  private
    Σ-path : ∀ {a b} {X : Set a} {Y : X → Set b}
           → {x x′ : X} {y : Y x} {y′ : Y x′}
           → (q : x ≡ x′) → transport Y q y ≡ y′
           → _≡_ {A = Σ X Y} (x , y) (x′ , y′)
    Σ-path refl refl = refl

  identity-fibre : (γ : Γ) (w : Output.family K γ) → I.comparison γ w ≡ w
  identity-fibre γ w =
    IdentityComparison.identity-choice fe Γ dΓ A K K γ w
    ∙ ChoiceIdentity.fibre-choice-id fe K γ w

  -- The total form lands in the pullback of the projection along id; this
  -- says which of its points is hit.
  identity-total : (z : Output.Total K)
                 → I.comparison-total z ≡ (Output.projection K z , (z , refl))
  identity-total z = Σ-path {Y = I.PulledFamily}
    (triangle I.comparison-over z)
    ( ap (λ r → transport I.PulledFamily r (snd (I.comparison-total z)))
         (sym (right-unit (triangle I.comparison-over z)))
    ∙ identity-fibre (Output.projection K z) (z , refl) )
