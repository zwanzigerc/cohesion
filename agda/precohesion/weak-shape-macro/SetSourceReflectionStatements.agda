{-# OPTIONS --cohesion --without-K --flat-split #-}

-- SIGNATURE PROBE for stage R of FABLE-PLAN-SET-SOURCE-01.txt: the closed
-- reflection as a left exact reflector of sets, and the shape of a closed
-- total. Claude (Fable), 14 November 2026.
-- Checked against the frozen fable-impl-22. NOT part of any tree.
--
-- It contains: the telescopes; the statements R1 to R4 AS TYPES; the
-- helpers without which a statement cannot be written (the square of the
-- pullback comparison, the map c η); and the type of every existing lemma
-- at the instance in which the plan uses it (the modules Legs). It
-- contains NO PROOF of a statement of the plan. Nothing is postulated.
module SetSourceReflectionStatements where

open import Foundations
open import CaptureContext using (Raise; raise; lower)
open import GlobalPrecohesion
  using (ShapeData; shape-data; ʃ; ʃ-set; ʃ-discrete; η; Recursor; Computes;
         Unique; discrete-elim)
open import GlobalPropositions using (FunExt₂)
open import LargeTarget using (LargeOn; module At)
open import TruncationDiscrete using (_⊎_; inl; inr)
open import PullbackSetFibers using () renaming (Pullback to PB)
open import OrdinaryTruncation
open import SmallQuotient
open import ClosedReflection
open import ClosedReflectionRaised using (module AtSupport)

------------------------------------------------------------------------
-- R1, R2, R3. Ordinary statements about the closed reflection. All
-- parameters and hypotheses are ordinary; one level.

module Gluing {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ)
  (T : PropTruncation ℓ) (P : Set ℓ) (P-prop : IsProp P) where

  open PropTruncation T
  open Reflection Q E T P P-prop

  -- R1. The comparison of the reflection of a pullback of sets with the
  --     pullback of the reflections. The pullback is written as
  --     ShapeReindexing writes its pulled total: Pullback g f is
  --     Σ (x : X) (Fiber g (f x)), with f the map of the bases.
  module Pullback {X Y Z : Set ℓ} (f : X → Z) (g : Y → Z) where

    D : Set ℓ
    D = PB g f

    H : Set ℓ
    H = PB (c-map g) (c-map f)

    pr₁ : D → X
    pr₁ d = fst d

    pr₂ : D → Y
    pr₂ d = fst (snd d)

    -- Helper, needed to write κ: the square on both sorts of generators.
    square : (z : c D) → c-map g (c-map pr₂ z) ≡ c-map f (c-map pr₁ z)
    square = generators-unique E c-set
      (λ z → c-map g (c-map pr₂ z)) (λ z → c-map f (c-map pr₁ z))
      (λ d → ap (c-map g) (c-map-inX pr₂ d) ∙ c-map-inX g (pr₂ d)
             ∙ ap inX (snd (snd d))
             ∙ sym (ap (c-map f) (c-map-inX pr₁ d) ∙ c-map-inX f (pr₁ d)))
      (λ p → ap (c-map g) (c-map-inP pr₂ p) ∙ c-map-inP g p
             ∙ sym (ap (c-map f) (c-map-inP pr₁ p) ∙ c-map-inP f p))

    -- THE comparison: its two projections are c-map pr₁ and c-map pr₂ by
    -- definition. Stage T uses this map and these two laws.
    κ : c D → H
    κ z = c-map pr₁ z , c-map pr₂ z , square z

    Statement-R1 : Set (lsuc ℓ)
    Statement-R1 = IsSet Z → Effective Q → IsEquiv κ

  -- R2. The reflection of a contractible type is contractible.
  Statement-R2 : Set (lsuc ℓ)
  Statement-R2 = {X : Set ℓ} → IsContr X → IsContr (c X)

  -- R3. Joint detection: a map of sets that is an equivalence under P and
  --     whose reflection is an equivalence is an equivalence.
  Statement-R3 : Set (lsuc ℓ)
  Statement-R3 = {X Y : Set ℓ} → IsSet X → IsSet Y → Effective Q
               → (h : X → Y) → (P → IsEquiv h) → IsEquiv (c-map h)
               → IsEquiv h

  -- The legs of R1 and R3, at the instances used.
  module Legs {X : Set ℓ} (effective : Effective Q) where

    cover : (z : c X) → ∥ Fiber inX z ⊎ Fiber inP z ∥
    cover = generator-cover

    test : (x x′ : X) → inX x ≡ inX x′ → ∥ (x ≡ x′) ⊎ P ∥
    test = Test.inX-test effective

    under-P : P → IsContr (c X)
    under-P = closed

    -- A proposition of the level is reached from a mere generator.
    into-prop : {A B : Set ℓ} → IsProp B → (A → B) → ∥ A ∥ → B
    into-prop = ∥-rec

------------------------------------------------------------------------
-- R1, R2, R3 for sets of level i and a support of level i ⊔ b: the forms
-- in which the later stages use them. The levels are crisp because Raise
-- asks for it; every other parameter and hypothesis is ordinary. cP,
-- unitP and pointP are, by definition, those of
-- ClosedReflectionRaised.AtSupport.

module AtLevel {@♭ i b : Level} (Q : Quotients (i ⊔ b))
  (E : Eliminates Q (i ⊔ b)) (T : PropTruncation (i ⊔ b))
  (P : Set (i ⊔ b)) (P-prop : IsProp P) where

  open Reflection Q E T P P-prop

  cP : Set i → Set (i ⊔ b)
  cP W = c (Raise b W)

  unitP : {W : Set i} → W → cP W
  unitP w = inX (raise w)

  pointP : {W : Set i} → P → cP W
  pointP = inP

  -- Helpers, needed to write the statements: the action on a map of
  -- level i and its two laws.
  up : {V W : Set i} → (V → W) → Raise b V → Raise b W
  up g r = raise (g (lower r))

  cP-map : {V W : Set i} → (V → W) → cP V → cP W
  cP-map g = c-map (up g)

  cP-map-unit : {V W : Set i} (g : V → W) (v : V)
              → cP-map g (unitP v) ≡ unitP (g v)
  cP-map-unit g v = c-map-inX (up g) (raise v)

  cP-map-point : {V W : Set i} (g : V → W) (p : P)
               → cP-map g (pointP p) ≡ pointP p
  cP-map-point g p = c-map-inP (up g) p

  module PullbackP {V₁ V₂ V₀ : Set i} (f : V₁ → V₀) (g : V₂ → V₀) where

    D₀ : Set i
    D₀ = PB g f

    HP : Set (i ⊔ b)
    HP = PB (cP-map g) (cP-map f)

    p₁ : D₀ → V₁
    p₁ d = fst d

    p₂ : D₀ → V₂
    p₂ d = fst (snd d)

    squareP : (z : cP D₀)
            → cP-map g (cP-map p₂ z) ≡ cP-map f (cP-map p₁ z)
    squareP = generators-unique E c-set
      (λ z → cP-map g (cP-map p₂ z)) (λ z → cP-map f (cP-map p₁ z))
      (λ r → ap (cP-map g) (c-map-inX (up p₂) r)
             ∙ c-map-inX (up g) (up p₂ r)
             ∙ ap inX (ap raise (snd (snd (lower r))))
             ∙ sym (ap (cP-map f) (c-map-inX (up p₁) r)
                    ∙ c-map-inX (up f) (up p₁ r)))
      (λ p → ap (cP-map g) (c-map-inP (up p₂) p) ∙ c-map-inP (up g) p
             ∙ sym (ap (cP-map f) (c-map-inP (up p₁) p)
                    ∙ c-map-inP (up f) p))

    κP : cP D₀ → HP
    κP z = cP-map p₁ z , cP-map p₂ z , squareP z

    Statement-R1P : Set (lsuc (i ⊔ b))
    Statement-R1P = IsSet V₀ → Effective Q → IsEquiv κP

  Statement-R2P : Set (lsuc i ⊔ b)
  Statement-R2P = {W : Set i} → IsContr W → IsContr (cP W)

  Statement-R3P : Set (lsuc (i ⊔ b))
  Statement-R3P = {V W : Set i} → IsSet V → IsSet W → Effective Q
                → (h : V → W) → (P → IsEquiv h) → IsEquiv (cP-map h)
                → IsEquiv h

------------------------------------------------------------------------
-- R4. The shape of a closed total, on the closed reflection of the old
-- carrier, with unit c η. W is at level i; the support at i ⊔ b.

module ClosedTotal {@♭ i b : Level} (@♭ Q : Quotients (i ⊔ b))
  (@♭ E : Eliminates Q (i ⊔ b)) (@♭ T : PropTruncation (i ⊔ b))
  (@♭ P : Set (i ⊔ b)) (@♭ P-prop : IsProp P) (@♭ dP : Discrete P)
  {@♭ W : Set i} (@♭ sW : ShapeData W) (@♭ cert : LargeOn b sW)
  (@♭ fe : FunExt₂ i (i ⊔ b)) where

  open Reflection Q E T P P-prop using (c-map; c-map-inX; c-map-inP)
  open AtSupport {i} {b} Q E T P P-prop dP

  -- Helper, needed to write the statement: the unit of the new shape.
  cη : cP W → cP (ʃ sW)
  cη = c-map (λ r → raise (η sW (lower r)))

  cη-unit : (w : W) → cη (unitP w) ≡ unitP (η sW w)
  cη-unit w = c-map-inX (λ r → raise (η sW (lower r))) (raise w)

  cη-point : (p : P) → cη (pointP p) ≡ pointP p
  cη-point = c-map-inP (λ r → raise (η sW (lower r)))

  -- The three fields that remain to be supplied.
  R4-Recursor : Set (lsuc (i ⊔ b))
  R4-Recursor = Recursor (cP W) (cP (ʃ sW)) cη

  R4-Computes : (@♭ r : R4-Recursor) → Set (lsuc (i ⊔ b))
  R4-Computes r = Computes (cP W) (cP (ʃ sW)) cη r

  R4-Unique : Set (lsuc (i ⊔ b))
  R4-Unique = Unique (cP W) (cP (ʃ sW)) cη

  -- With them the shape datum is this term, and its carrier and unit are
  -- the stated ones by conversion.
  module Assembled (@♭ r : R4-Recursor) (@♭ r-η : R4-Computes r)
    (@♭ u : R4-Unique) where

    closed-shape : ShapeData (cP W)
    closed-shape = shape-data (cP (ʃ sW)) cP-set
      (cP-discrete (ʃ-discrete sW)) cη r r-η u

    carrier-is : ʃ closed-shape ≡ cP (ʃ sW)
    carrier-is = refl

    unit-is : (z : cP W) → η closed-shape z ≡ cη z
    unit-is z = refl

  -- The legs, at the instances used: for a crisp discrete set D of the
  -- higher level and a crisp g : cP W → D.
  module Legs (@♭ D : Set (i ⊔ b)) (@♭ D-set : IsSet D)
    (@♭ D-discrete : Discrete D) (@♭ g : cP W → D) where

    private
      module A = At b cert D D-set D-discrete

    -- the large recursor of the ORIGINAL shape at g on the units
    r₀ : ʃ sW → D
    r₀ = A.recLarge (λ w → g (unitP w))

    r₀-η : (w : W) → r₀ (η sW w) ≡ g (unitP w)
    r₀-η = A.recLarge-η (λ w → g (unitP w))

    -- large uniqueness, with the mixed extensionality
    large-unique : (@♭ k k′ : ʃ sW → D)
                 → (@♭ e : (w : W) → k (η sW w) ≡ k′ (η sW w))
                 → (z : ʃ sW) → k z ≡ k′ z
    large-unique = A.recLarge-unique fe

    -- induction on the discrete support, the ordinary z kept in the motive
    on-support : (M : P → Set (i ⊔ b)) → ((@♭ p : P) → M p)
               → (p : P) → M p
    on-support = discrete-elim dP

    -- the two-generator property of the reflection of the OLD carrier,
    -- into the set D, which need not be closed
    extend : (k : ʃ sW → D) (m : P → D)
           → ((z : ʃ sW) (p : P) → k z ≡ m p) → cP (ʃ sW) → D
    extend = CoconeP.extendP E (own-level T) D-set

    extend-unit : (k : ʃ sW → D) (m : P → D)
                → (a : (z : ʃ sW) (p : P) → k z ≡ m p)
                → (s : ʃ sW) → extend k m a (unitP s) ≡ k s
    extend-unit = CoconeP.extendP-unit E (own-level T) D-set

    extend-point : (k : ʃ sW → D) (m : P → D)
                 → (a : (z : ʃ sW) (p : P) → k z ≡ m p)
                 → (p : P) → extend k m a (pointP p) ≡ m p
    extend-point = CoconeP.extendP-point E (own-level T) D-set

    -- the gluing of the two generators of cP W
    glue : (w : W) (p : P) → unitP w ≡ pointP p
    glue = glueP

    agree : (u v : cP W → D)
          → ((w : W) → u (unitP w) ≡ v (unitP w))
          → ((p : P) → u (pointP p) ≡ v (pointP p))
          → (z : cP W) → u z ≡ v z
    agree = generatorsP-unique E D-set

    -- the same on the reflection of the old carrier, for uniqueness
    agree-on-carrier : (u v : cP (ʃ sW) → D)
                     → ((s : ʃ sW) → u (unitP s) ≡ v (unitP s))
                     → ((p : P) → u (pointP p) ≡ v (pointP p))
                     → (z : cP (ʃ sW)) → u z ≡ v z
    agree-on-carrier = generatorsP-unique E D-set
