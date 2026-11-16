{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The codiscrete power: ♯ (F → A) ≃ (F → ♯ A) for a discrete F, and the
-- comparison that it induces between independently chosen shapes.
-- Claude (Fable), 14 November 2026; fable-impl-20 (HANDOFF-36, section 6;
-- CODISCRETE-POWER-NATIVE-ROUTE-01, sections 1 to 4, whose route this is).
--
-- Nothing is postulated, and nothing is declared. No definition of this
-- module takes or uses a product axiom, the Nullstellensatz, propositional
-- extensionality, a truncation, a larger-target certificate or a
-- stability hypothesis. (The types of some of these are defined in the
-- imported GlobalPrecohesion; none is named in a type of this module.)
--
-- DATA, all crisp, at ONE level ℓ: types F and A, and dF : Discrete F.
-- Neither F nor A is asked to be a set, and A is not asked to be discrete.
--
-- Source (no hypothesis):
--   E = F → ♯ A,   Y = ♯ (F → A)
--   e : Y → E      evaluation under ♯: e q x = sharp-map (λ g → g x) q
--   b : E → Y      the field of b g is defined by induction on the
--                  discrete type F, INSIDE the field of ♯
--   e-unit         e (sharp-unit g) x ≡ sharp-unit (g x), by computation
--   b-at           the computation rule of b at a crisp g and a crisp x
--
-- Inverse (crisp fe : FunExt₂ ℓ ℓ):
--   e-b, b-e       the two inverse laws, as paths of ordinary points
--   e-is-equiv     IsEquiv e
--
-- Transfer (the same fe; three INDEPENDENT crisp shape data):
--   sX : ShapeData (♯ A),  sE : ShapeData (F → ♯ A),
--   sY : ShapeData (♯ (F → A))
--   alpha, beta    the recursors of sY and sE at η sE ∘ e and η sY ∘ b,
--                  with their unit laws; mutually inverse by the
--                  uniqueness of sY and of sE
--   sigma          κ dF sX sE ∘ alpha, where κ is the EXISTING continuity
--                  comparison of GlobalPrecohesion for dF, sX and sE
--   sigma-unit     sigma (η sY (sharp-unit g)) x ≡ η sX (sharp-unit (g x))
--   sigma-injective   from MonoC dF sX sE, an ORDINARY argument
--   unit-cong         from MonoC: if η sX (sharp-unit (g x)) and
--                     η sX (sharp-unit (h x)) agree for every x, then
--                     η sY (sharp-unit g) ≡ η sY (sharp-unit h)
--
-- WHY b IS WRITTEN AS IT IS. In the field of a point of ♯ every usable
-- variable counts as crisp, so there g is crisp. A variable that a λ binds
-- AFTER the field has been entered is an ordinary variable again: the term
-- λ x → sharp-extract (g x) is refused as a function F → A
-- (CodiscreteOrdinaryLambda is that case). The induction principle of the
-- discrete type F asks for a function of a CRISP x, and for a crisp x the
-- extraction is allowed. No map ♯ A → A on ordinary points is used or
-- defined.
--
-- WHERE fe IS USED, AND WHY IT IS CRISP. In Inverse it is used four
-- times: in SharpPath.sharp-path-extract (twice), and to make a path of
-- functions from a pointwise one (twice). None of these uses needs a crisp
-- fe. In Transfer the two inverse laws are premises of the uniqueness
-- rules of sY and of sE, which take their premises crisply; so there fe is
-- crisp. It is a parameter of both modules, crisp in both, so that
-- Transfer can open Inverse.
--
-- WHAT IS NOT IDENTIFIED. sX, sE and sY keep their carriers and units. A
-- shape datum of F → A, which a client may hold in order to prove that
-- type discrete (FixedPower), is a FOURTH datum and does not occur here.
-- alpha is the comparison of two chosen shapes that the equivalence e
-- induces; it is not an arbitrary injection between their carriers.
module CodiscretePower where

open import Foundations
open import NativeSharp
  using (♯; ε; sharp-unit; sharp-extract; sharp-map)
open import Adjointify using (quasi-inverse)
open import GlobalPrecohesion
  using (discrete-elim; discrete-elim-β; ShapeData; ʃ; ʃ-set; ʃ-discrete;
         η; rec; rec-η; unique; κ; κ-η; MonoC)
open import GlobalPropositions using (FunExt₂)
open import SharpPath using (sharp-path-extract)

------------------------------------------------------------------------
-- 1. The two maps. No hypothesis.

module Source {@♭ ℓ : Level} {@♭ F A : Set ℓ} (@♭ dF : Discrete F) where

  E : Set ℓ
  E = F → ♯ A

  Y : Set ℓ
  Y = ♯ (F → A)

  -- Evaluation under ♯. Its arguments are ordinary.
  e : Y → E
  e q x = sharp-map (λ g → g x) q

  -- Inside the field g is crisp; the induction on F supplies a crisp x.
  b : E → Y
  b g .ε = discrete-elim dF (λ _ → A) (λ x → sharp-extract (g x))

  -- The unit law, by computation.
  e-unit : (g : F → A) (x : F) → e (sharp-unit g) x ≡ sharp-unit (g x)
  e-unit g x = refl

  -- Evaluation commutes with extraction, by computation.
  e-extract : (@♭ q : Y) (@♭ x : F)
            → sharp-extract (e q x) ≡ sharp-extract q x
  e-extract q x = refl

  -- The computation rule of b: that of the induction on F. It is a path,
  -- and it is stated at a crisp x.
  b-at : (@♭ g : E) (@♭ x : F)
       → sharp-extract (b g) x ≡ sharp-extract (g x)
  b-at g x = discrete-elim-β dF (λ _ → A) (λ x′ → sharp-extract (g x′)) x

------------------------------------------------------------------------
-- 2. The two inverse laws.

module Inverse {@♭ ℓ : Level} {@♭ F A : Set ℓ} (@♭ dF : Discrete F)
  (@♭ fe : FunExt₂ ℓ ℓ) where

  open Source {A = A} dF public

  private
    -- A point of ♯ (e (b g) x ≡ g x). In its field g and x are crisp, so
    -- b-at applies. The two sides of the path are e (b g) x and g x by the
    -- eta rule of ♯.
    e-b-sharp : (g : E) (x : F) → ♯ (e (b g) x ≡ g x)
    e-b-sharp g x .ε = ap sharp-unit (b-at g x)

  e-b : (g : E) → e (b g) ≡ g
  e-b g = fe (λ x → sharp-path-extract fe (e (b g) x) (g x) (e-b-sharp g x))

  private
    -- For a crisp q the two underlying functions F → A agree: at a crisp
    -- x by b-at and e-extract, at every x by induction on F.
    b-e-under : (@♭ q : Y) → sharp-extract (b (e q)) ≡ sharp-extract q
    b-e-under q =
      fe (discrete-elim dF
            (λ x → sharp-extract (b (e q)) x ≡ sharp-extract q x)
            (λ x → b-at (e q) x))

    -- In the field q is crisp.
    b-e-sharp : (q : Y) → ♯ (b (e q) ≡ q)
    b-e-sharp q .ε = ap sharp-unit (b-e-under q)

  b-e : (q : Y) → b (e q) ≡ q
  b-e q = sharp-path-extract fe (b (e q)) q (b-e-sharp q)

  e-is-equiv : IsEquiv e
  e-is-equiv = quasi-inverse b e-b b-e

------------------------------------------------------------------------
-- 3. The comparison of three independently chosen shapes.

module Transfer {@♭ ℓ : Level} {@♭ F A : Set ℓ} (@♭ dF : Discrete F)
  (@♭ fe : FunExt₂ ℓ ℓ)
  (@♭ sX : ShapeData (♯ A))
  (@♭ sE : ShapeData (F → ♯ A))
  (@♭ sY : ShapeData (♯ (F → A))) where

  open Inverse {A = A} dF fe public

  -- The recursors of the ORIGINAL data, at the units composed with e, b.
  alpha : ʃ sY → ʃ sE
  alpha = rec sY (ʃ sE) (ʃ-set sE) (ʃ-discrete sE) (λ y → η sE (e y))

  alpha-η : (y : Y) → alpha (η sY y) ≡ η sE (e y)
  alpha-η = rec-η sY (ʃ sE) (ʃ-set sE) (ʃ-discrete sE) (λ y → η sE (e y))

  beta : ʃ sE → ʃ sY
  beta = rec sE (ʃ sY) (ʃ-set sY) (ʃ-discrete sY) (λ z → η sY (b z))

  beta-η : (z : E) → beta (η sE z) ≡ η sY (b z)
  beta-η = rec-η sE (ʃ sY) (ʃ-set sY) (ʃ-discrete sY) (λ z → η sY (b z))

  -- Uniqueness takes two crisp maps and a crisp proof that they agree on
  -- the units. The proof is made of the unit laws and of an inverse law
  -- of section 2; this is where fe has to be crisp.
  beta-alpha : (s : ʃ sY) → beta (alpha s) ≡ s
  beta-alpha =
    unique sY (ʃ sY) (ʃ-set sY) (ʃ-discrete sY)
      (λ s → beta (alpha s)) (λ s → s)
      (λ y → ap beta (alpha-η y) ∙ beta-η (e y) ∙ ap (η sY) (b-e y))

  alpha-beta : (t : ʃ sE) → alpha (beta t) ≡ t
  alpha-beta =
    unique sE (ʃ sE) (ʃ-set sE) (ʃ-discrete sE)
      (λ t → alpha (beta t)) (λ t → t)
      (λ z → ap alpha (beta-η z) ∙ alpha-η (b z) ∙ ap (η sE) (e-b z))

  alpha-is-equiv : IsEquiv alpha
  alpha-is-equiv = quasi-inverse beta alpha-beta beta-alpha

  alpha-injective : (s t : ʃ sY) → alpha s ≡ alpha t → s ≡ t
  alpha-injective s t h = sym (beta-alpha s) ∙ ap beta h ∙ beta-alpha t

  -- The existing continuity comparison for dF, sX and sE, and its
  -- composite with alpha.
  kappa : ʃ sE → F → ʃ sX
  kappa = κ dF sX sE

  sigma : ʃ sY → F → ʃ sX
  sigma s = kappa (alpha s)

  -- The coaugmentations A → ʃ sX and (F → A) → ʃ sY.
  unit-A : A → ʃ sX
  unit-A a = η sX (sharp-unit a)

  unit-Q : (F → A) → ʃ sY
  unit-Q g = η sY (sharp-unit g)

  -- From sigma after the unit of F → A to the unit of A, pointwise, for
  -- ORDINARY g and x: the unit law of alpha, then that of κ, then e-unit.
  sigma-unit : (g : F → A) (x : F) → sigma (unit-Q g) x ≡ unit-A (g x)
  sigma-unit g x =
    ap (λ z → kappa z x) (alpha-η (sharp-unit g))
    ∙ κ-η dF sX sE (e (sharp-unit g)) x
    ∙ ap (η sX) (e-unit g x)

  -- MonoC is used after the maps have been made; it need not be crisp.
  sigma-injective : MonoC dF sX sE
                  → (s t : ʃ sY) → sigma s ≡ sigma t → s ≡ t
  sigma-injective mc s t h = alpha-injective s t (mc (alpha s) (alpha t) h)

  -- The consequence that the principal filter uses. Two functions F → A
  -- whose values have the same unit in ʃ sX, pointwise, have the same unit
  -- in ʃ sY: the two unit laws of sigma, extensionality for functions
  -- F → ʃ sX, and the cancellation of sigma.
  unit-cong : MonoC dF sX sE
            → (g h : F → A) → ((x : F) → unit-A (g x) ≡ unit-A (h x))
            → unit-Q g ≡ unit-Q h
  unit-cong mc g h agree =
    sigma-injective mc (unit-Q g) (unit-Q h)
      (fe (λ x → sigma-unit g x ∙ agree x ∙ sym (sigma-unit h x)))
