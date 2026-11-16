{-# OPTIONS --cohesion --without-K --flat-split #-}

-- What function extensionality and propositional extensionality give for
-- the propositions of one universe: being a proposition is a proposition,
-- propositions with the same underlying type are equal, and HProp i is a
-- set. Claude (Fable), 14 November 2026; fable-impl-19 (HANDOFF-35, item 2).
--
-- Nothing is postulated: both principles are HYPOTHESES, written in the
-- type of every statement that uses them, at the levels it uses them.
--   FunExt₂ i i   GlobalPropositions.FunExt₂, the village's level-indexed
--                 statement, reused and not restated;
--   PropExt i     SmallPropositions.PropExt, about ordinary propositions.
-- All arguments here are ordinary; a caller that needs a crisp result
-- passes crisp hypotheses.
--
-- This module has --flat-split only because it imports GlobalPropositions
-- for FunExt₂, and the flag is infective. It matches on no crisp argument
-- and uses no modality. The proofs are ordinary type theory.
--
-- Proof arguments adapted on 14 November 2026 from Martín Escardó and
-- contributors’ TypeTopology, distributed under the GNU General Public
-- License version 3; see ../notices/TypeTopology-LICENSE.txt and ../SOURCES.md.
-- Reference proofs read for this port (TypeTopology, copies in the village
-- folder classifier-reuse-source-01/; re-proved in the village's
-- representations, not imported):
--   UF/SubtypeClassifier.lagda:36-41, 202-209    to-Ω-＝, Ω-extensionality
--   UF/SubtypeClassifier-Properties.lagda:24-57  Ω-is-set
-- As there, sethood of the propositions of level i needs function
-- extensionality at (i, i) only, not at the next level.
module SmallPropositionLaws where

open import Foundations
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions

private
  ap₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C)
      → {x x′ : A} {y y′ : B} → x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
  ap₂ f refl refl = refl

-- A product of propositions is a proposition.
pi-is-prop : ∀ {a b} → FunExt₂ a b → {X : Set a} {Y : X → Set b}
           → ((x : X) → IsProp (Y x)) → IsProp ((x : X) → Y x)
pi-is-prop fe h f g = fe (λ x → h x (f x) (g x))

-- Being a proposition is a proposition.
is-prop-is-prop : ∀ {a} → FunExt₂ a a → {A : Set a} → IsProp (IsProp A)
is-prop-is-prop fe h k =
  fe (λ x → fe (λ y → prop-is-set h x y (h x y) (k x y)))

-- Propositions with equal underlying types are equal.
hprop-path : ∀ {i} → FunExt₂ i i → {p q : HProp i} → fst p ≡ fst q → p ≡ q
hprop-path fe = subtype-path (λ P → is-prop-is-prop fe)

-- Logically equivalent propositions are equal.
hprop-ext : ∀ {i} → FunExt₂ i i → PropExt i → {p q : HProp i}
          → (fst p → fst q) → (fst q → fst p) → p ≡ q
hprop-ext fe pe {p} {q} f g = hprop-path fe (pe (snd p) (snd q) f g)

-- The propositions of level i form a set: every identity type has a
-- constant endomap, through the two implications.
HProp-is-set : ∀ {i} → FunExt₂ i i → PropExt i → IsSet (HProp i)
HProp-is-set {i} fe pe = collapsible-set collapse constant
  where
  collapse : {p q : HProp i} → p ≡ q → p ≡ q
  collapse e = hprop-ext fe pe (hprop-forward e) (hprop-backward e)

  constant : {p q : HProp i} (e e′ : p ≡ q) → collapse e ≡ collapse e′
  constant {p} {q} e e′ =
    ap₂ (hprop-ext fe pe)
      (pi-is-prop fe (λ _ → snd q) (hprop-forward e) (hprop-forward e′))
      (pi-is-prop fe (λ _ → snd p) (hprop-backward e) (hprop-backward e′))
