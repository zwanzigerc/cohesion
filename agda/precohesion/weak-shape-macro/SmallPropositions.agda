{-# OPTIONS --safe --without-K --cohesion #-}

-- Small helpers about propositions and sets, and the type of the
-- propositions of one universe. Claude (Fable), 14 November 2026;
-- fable-impl-19 (HANDOFF-35, item 2; the helper exports that
-- CLASSIFIER-CORE-M16-SOURCE-READINESS-01 lists as missing).
--
-- Literally --safe. Ordinary type theory: nothing here uses a modality, and
-- no extensionality principle is used or assumed. (--cohesion is in the
-- options because Foundations has it and the flag is infective.) The
-- statements that need function extensionality are in
-- SmallPropositionLaws, with the hypothesis written in their types.
--
-- Two of these arguments exist in the village inside modules with
-- --flat-split: prop-set, a PRIVATE definition of GlobalPropositions, and
-- the Hedberg argument of DecidableBase, stated there for decidable
-- equality. Those are not changed. A module without the flag cannot
-- import a module that has it, and a private name cannot be imported at
-- all.
module SmallPropositions where

open import Foundations
open import NativeSharp using (transport)
open import Adjointify using (quasi-inverse)

------------------------------------------------------------------------
-- 1. Propositions are sets; retracts and subtypes.

private
  cancel : ∀ {a} {A : Set a} {x y : A} (e : x ≡ y) → sym e ∙ e ≡ refl
  cancel refl = refl

prop-is-set : ∀ {a} {A : Set a} → IsProp A → IsSet A
prop-is-set {A = A} h x y p q = lemma p ∙ sym (lemma q)
  where
  lemma : {z : A} (r : x ≡ z) → r ≡ sym (h x x) ∙ h x z
  lemma refl = sym (cancel (h x x))

retract-is-prop : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (g : B → A)
                → ((x : A) → g (f x) ≡ x) → IsProp B → IsProp A
retract-is-prop f g h B-prop x y =
  sym (h x) ∙ ap g (B-prop (f x) (f y)) ∙ h y

-- Two points of a Σ over a family of propositions are equal as soon as
-- their first components are.
subtype-path : ∀ {a b} {A : Set a} {B : A → Set b}
             → ((x : A) → IsProp (B x))
             → {u w : Σ A B} → fst u ≡ fst w → u ≡ w
subtype-path B-prop {x , y} {.x , z} refl = ap (λ t → x , t) (B-prop x y z)

-- A map between propositions with a map back is an equivalence. The
-- inverse of the result is g, by computation.
prop-equiv : ∀ {a b} {A : Set a} {B : Set b} → IsProp A → IsProp B
           → (f : A → B) (g : B → A) → IsEquiv f
prop-equiv A-prop B-prop f g =
  quasi-inverse g (λ y → B-prop (f (g y)) y) (λ x → A-prop (g (f x)) x)

-- For a map into a set, injectivity gives proposition fibres.
injective-fibres : ∀ {a b} {A : Set a} {B : Set b} (f : A → B)
                 → IsSet B → ((x y : A) → f x ≡ f y → x ≡ y)
                 → (b : B) → IsProp (Fiber f b)
injective-fibres f B-set inj b (x , p) (y , q) =
  subtype-path (λ z → B-set (f z) b) (inj x y (p ∙ sym q))

------------------------------------------------------------------------
-- 2. A type whose identity types have constant endomaps is a set
--    (Hedberg's argument in its local form; Kraus, Escardó, Coquand and
--    Altenkirch). TypeTopology uses this lemma, under the name
--    Id-collapsibles-are-sets, for the sethood of its Ω
--    (UF/SubtypeClassifier-Properties.lagda:24-57, read); its proof there
--    is in a module that was not supplied. The proof below is the
--    argument of DecidableBase, with the decision replaced by the
--    constant map.

collapsible-set : ∀ {a} {A : Set a}
                → (c : {x y : A} → x ≡ y → x ≡ y)
                → ({x y : A} (p q : x ≡ y) → c p ≡ c q)
                → IsSet A
collapsible-set {A = A} c constant x y p q =
  recover p ∙ ap (λ r → sym (c refl) ∙ r) (constant p q) ∙ sym (recover q)
  where
  recover : {z : A} (r : x ≡ z) → r ≡ sym (c refl) ∙ c r
  recover refl = sym (cancel (c refl))

------------------------------------------------------------------------
-- 3. The propositions of level i, and propositional extensionality for
--    them. Both are ORDINARY types: P, Q and the two implications in
--    PropExt are ordinary variables.
--
--    HProp i has the same definition as LargeTargetClassifier.Ω i (the
--    AMBIENT type of propositions). It is NOT the base classifier; that
--    is BaseClassifier.O.

HProp : (i : Level) → Set (lsuc i)
HProp i = Σ (Set i) IsProp

PropExt : (i : Level) → Set (lsuc i)
PropExt i = {P Q : Set i} → IsProp P → IsProp Q → (P → Q) → (Q → P) → P ≡ Q

-- The two implications that an identification of propositions gives.
hprop-forward : ∀ {i} {p q : HProp i} → p ≡ q → fst p → fst q
hprop-forward {p = p} e = transport (λ r → fst p → fst r) e (λ x → x)

hprop-backward : ∀ {i} {p q : HProp i} → p ≡ q → fst q → fst p
hprop-backward {p = p} e = transport (λ r → fst r → fst p) e (λ x → x)
