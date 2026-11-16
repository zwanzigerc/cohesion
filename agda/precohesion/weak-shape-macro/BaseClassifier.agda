{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The carrier of the base classifier, its decoding and its truth point.
-- Claude (Fable), 14 November 2026; fable-impl-19 (HANDOFF-35, item 1;
-- BASE-CLASSIFIER-NATIVE-AUDIT-01, sections 1 and 8.1).
--
-- Nothing is postulated here, and NO hypothesis is taken: no definition
-- of this module mentions function extensionality or propositional
-- extensionality, a shape or a truncation, and nothing is resized. That
-- is a statement about what is USED. The import closure does contain
-- definitions of such statement TYPES: Foundations defines FunExt,
-- BoxIdentity and PropositionalTruncation, and SmallPropositions defines
-- PropExt (only the name HProp is imported from it). GlobalPropositions,
-- where FunExt₂ is defined, is not in the import closure. Sethood and the
-- other laws are in BaseClassifierLaws, which takes its two hypotheses as
-- parameters and proves facts about the definitions of THIS module
-- without making copies of them.
--
-- For a crisp level i:
--   HProp i = Σ (P : Set i). IsProp P     : Set (lsuc i)   (SmallPropositions)
--   U i     = ♭ (HProp i)                 : Set (lsuc i)
--   d       : U i → Set i,   d (box (P , h)) = Discrete P
--   C i     = Σ (q : U i). d q            : Set (lsuc i)
--   O i     = ♭ (C i)                     : Set (lsuc i)
--   El      : O i → Set i                 by the two counits
--   top     : O i                         the unit of level i
--
-- Why two ♭. `Discrete` takes a CRISP type, so  Σ (P : Set i). Discrete P
-- is not a type of Agda: P is an ordinary variable. The inner ♭ makes the
-- proposition crisp, so that the clause of d is well typed. The outer ♭
-- makes O i discrete (flat-discrete) without any assumption on C i, and
-- makes a crisp point of O i contain a crisp proof of discreteness.
--
-- O i is NOT ♭ (HProp i), and it is not the ambient type of propositions
-- LargeTargetClassifier.Ω i. `decode` is the comparison O i → HProp i.
--
-- At a CRISP code r the decoded type is discrete, by the stored proof
-- (El-discrete). For an ordinary r the type  Discrete (El r)  cannot be
-- written, since El r is then not a crisp type; one eliminates r instead
-- (O-elim), which gives crisp P, h and dP.
module BaseClassifier where

open import Foundations
open import CaptureContext using (CrispUnitAt; end-at; unit-at-discrete)
open import FlatContext using (flat-discrete)
open import SmallPropositions using (HProp)

------------------------------------------------------------------------
-- 1. The carrier.

U : (@♭ i : Level) → Set (lsuc i)
U i = ♭ (HProp i)

-- The pattern binds P crisply; so Discrete P is well formed.
d : {@♭ i : Level} → U i → Set i
d (box (P , h)) = Discrete P

C : (@♭ i : Level) → Set (lsuc i)
C i = Σ (U i) d

O : (@♭ i : Level) → Set (lsuc i)
O i = ♭ (C i)

-- The outer ♭ makes it discrete; nothing is assumed about C i.
O-discrete : {@♭ i : Level} → Discrete (O i)
O-discrete {i} = flat-discrete (C i)

------------------------------------------------------------------------
-- 2. Decoding, by the two counits.

decode : {@♭ i : Level} → O i → HProp i
decode r = counit (fst (counit r))

El : {@♭ i : Level} → O i → Set i
El r = fst (decode r)

El-is-prop : {@♭ i : Level} (r : O i) → IsProp (El r)
El-is-prop r = snd (decode r)

------------------------------------------------------------------------
-- 3. Codes. A crisp proposition of level i with a crisp proof of
--    discreteness is a point of O i, and every point is of this form.

code : {@♭ i : Level} (@♭ P : Set i) (@♭ h : IsProp P) (@♭ dP : Discrete P)
     → O i
code P h dP = box (box (P , h) , dP)

-- El (code P h dP) is P, and El-is-prop (code P h dP) is h, by computation.

O-elim : {@♭ i : Level} {b : Level} (M : O i → Set b)
       → ((@♭ P : Set i) (@♭ h : IsProp P) (@♭ dP : Discrete P)
          → M (code P h dP))
       → (r : O i) → M r
O-elim M k (box (box (P , h) , dP)) = k P h dP

-- The decoded proposition of a CRISP code is discrete: the stored proof.
El-discrete : {@♭ i : Level} (@♭ r : O i) → Discrete (El r)
El-discrete (box (box (P , h) , dP)) = dP

------------------------------------------------------------------------
-- 4. Truth: the one-point type of level i. No lifting and no resizing;
--    CrispUnitAt i is a data type of Set i.

unit-at-is-prop : {@♭ i : Level} → IsProp (CrispUnitAt i)
unit-at-is-prop end-at end-at = refl

top : {@♭ i : Level} → O i
top {i} = code (CrispUnitAt i) unit-at-is-prop unit-at-discrete

-- El top is CrispUnitAt i by computation, so this is well typed.
top-holds : {@♭ i : Level} → El (top {i})
top-holds = end-at
