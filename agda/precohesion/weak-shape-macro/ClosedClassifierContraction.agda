{-# OPTIONS --cohesion --without-K --flat-split #-}

-- SET-SOURCE STAGE C5 (with the binary meet): the shape of the sharp of the
-- closed classifier is contractible. Opus, 14 November 2026;
-- opus-closed-limits-01 (delta 05), implementing FABLE-PLAN-SET-SOURCE-01
-- §6.3 (CLOSED-CLASSIFIER-CONNECTED-NATIVE-ROUTE-01, sections 2–7).
--
-- 1. The binary meet on O ℓ (NEW; fable-impl-20 has only the unary join):
--      meet r s = code (El r × El s), by matching both codes;
--      meet-out / meet-in decode it; left-top : meet top q ≡ q;
--      absorb : (@♭ r q) → (@♭ El r → El q) → meet r q ≡ r   (Laws.code-ext).
-- 2. C5, generic in the closed data (plan §2 design rule; the kernel passes
--    its OWN instances, so no second copy of the support is compared —
--    §13.1): crisp C : Set k with C-discrete, inclusion, truth-point, the
--    code p, the implication El p → El (inclusion c), the closed retraction
--    r with retracts and r-top; choices sOj, sOO, sC. Ordinary hypotheses:
--    membership : eⱼ p ≡ eⱼ top, the product law, the Nullstellensatz of sC.
--      contractible : IsContr (ʃ sC)
--    Steps (plan §6.3): mix by copattern, M = rec sOO (same-level); meets
--    are respected (product law injectivity); upward closure
--    eⱼ (inclusion c) ≡ eⱼ top (left-top, membership, absorb at a crisp c by
--    discrete-elim); Tr = rec sOj (same-level) moves it to eC c ≡ eC truth-
--    point; the Nullstellensatz is eliminated into the proposition
--    centre ≡ z, its witness (box t₀ , e) having t₀ crisp.
-- Only same-level recursors: no certificate, no large uniqueness. No
-- postulate. Extensionality only through Laws.code-ext (fe, pe at j).
module ClosedClassifierContraction where

open import Foundations
open import NativeSharp using (♯; ε; sharp-unit; sharp-map; sharp-extract)
open import ShapeElim using (module SigmaDiscrete)
open import GlobalPrecohesion
  using (ShapeData; ʃ; ʃ-set; ʃ-discrete; η; rec; rec-η; points-to-pieces;
         Nullstellensatz; PreservesProduct; compare; compare-η; discrete-elim)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions using (PropExt)
open import BaseClassifier using (O; El; El-is-prop; code; top)
open import BaseClassifierLaws using (module Laws)
open import CaptureContext using (CrispUnitAt; end-at)

------------------------------------------------------------------------
-- 1. The binary meet.

×-prop : ∀ {a b} {A : Set a} {B : Set b} → IsProp A → IsProp B → IsProp (A × B)
×-prop hA hB (a , b) (a′ , b′) = pair-path (hA a a′) (hB b b′)

module Meet {@♭ ℓ : Level} (@♭ fe : FunExt₂ ℓ ℓ) (@♭ pe : PropExt ℓ) where

  open Laws fe pe using (code-ext)

  meet : O ℓ → O ℓ → O ℓ
  meet (box (box (P , h) , dP)) (box (box (Q , k) , dQ)) =
    code (P × Q) (×-prop h k) (SigmaDiscrete.discrete dP (λ _ → dQ))

  meet-out : (r s : O ℓ) → El (meet r s) → El r × El s
  meet-out (box (box (P , h) , dP)) (box (box (Q , k) , dQ)) x = x

  meet-in : (r s : O ℓ) → El r × El s → El (meet r s)
  meet-in (box (box (P , h) , dP)) (box (box (Q , k) , dQ)) x = x

  left-top : (q : O ℓ) → meet top q ≡ q
  left-top (box (box (Q , k) , dQ)) =
    code-ext (meet top (code Q k dQ)) (code Q k dQ) snd (λ x → end-at , x)

  absorb : (@♭ r q : O ℓ) (@♭ imp : El r → El q) → meet r q ≡ r
  absorb (box (box (P , h) , dP)) (box (box (Q , k) , dQ)) imp =
    code-ext (meet (code P h dP) (code Q k dQ)) (code P h dP) fst (λ x → x , imp x)

------------------------------------------------------------------------
-- 2. C5.

module C5 {@♭ i : Level}
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) (@♭ pe-j : PropExt (lsuc i))
  (@♭ C : Set (lsuc (lsuc i))) (@♭ C-discrete : Discrete C)
  (@♭ inclusion : C → O (lsuc i)) (@♭ truth-point : C)
  (@♭ p : O (lsuc i))
  (@♭ imp : (c : C) → El p → El (inclusion c))
  (@♭ r : O (lsuc i) → C)
  (@♭ retracts : (c : C) → r (inclusion c) ≡ c)
  (@♭ r-top : r top ≡ truth-point)
  (@♭ sOj : ShapeData (♯ (O (lsuc i))))
  (@♭ sOO : ShapeData (♯ (O (lsuc i)) × ♯ (O (lsuc i))))
  (@♭ sC : ShapeData (♯ C)) where

  open Meet fe-j pe-j

  eⱼ : O (lsuc i) → ʃ sOj
  eⱼ q = η sOj (sharp-unit q)

  eC : C → ʃ sC
  eC c = η sC (sharp-unit c)

  -- 2. mix and M.
  mix : ♯ (O (lsuc i)) × ♯ (O (lsuc i)) → ♯ (O (lsuc i))
  mix w .ε = meet (fst w .ε) (snd w .ε)

  M : ʃ sOO → ʃ sOj
  M = rec sOO (ʃ sOj) (ʃ-set sOj) (ʃ-discrete sOj) (λ w → η sOj (mix w))

  M-η : (a b : O (lsuc i)) → M (η sOO (sharp-unit a , sharp-unit b)) ≡ eⱼ (meet a b)
  M-η a b = rec-η sOO (ʃ sOj) (ʃ-set sOj) (ʃ-discrete sOj) (λ w → η sOj (mix w))
    (sharp-unit a , sharp-unit b)

  -- The absorption at the code p, for every c (crisp first).
  absorb-p : (c : C) → meet p (inclusion c) ≡ p
  absorb-p = discrete-elim C-discrete (λ c → meet p (inclusion c) ≡ p)
    (λ c → absorb p (inclusion c) (imp c))

  -- Tr and its unit law.
  Tr : ʃ sOj → ʃ sC
  Tr = rec sOj (ʃ sC) (ʃ-set sC) (ʃ-discrete sC) (λ x → η sC (sharp-map r x))

  Tr-η : (o : O (lsuc i)) → Tr (eⱼ o) ≡ eC (r o)
  Tr-η o = rec-η sOj (ʃ sC) (ʃ-set sC) (ʃ-discrete sC) (λ x → η sC (sharp-map r x))
    (sharp-unit o)

  module _ (membership : eⱼ p ≡ eⱼ top)
           (pp : PreservesProduct sOj sOj sOO) where

    -- 3. Meets are respected.
    respects : {a a′ b b′ : O (lsuc i)} → eⱼ a ≡ eⱼ a′ → eⱼ b ≡ eⱼ b′
             → eⱼ (meet a b) ≡ eⱼ (meet a′ b′)
    respects {a} {a′} {b} {b′} ea eb =
      sym (M-η a b) ∙ ap M units ∙ M-η a′ b′
      where
      units : η sOO (sharp-unit a , sharp-unit b) ≡ η sOO (sharp-unit a′ , sharp-unit b′)
      units = sym (retraction pp _)
        ∙ ap (inverse pp)
            (compare-η sOj sOj sOO (sharp-unit a) (sharp-unit b)
             ∙ pair-path ea eb
             ∙ sym (compare-η sOj sOj sOO (sharp-unit a′) (sharp-unit b′)))
        ∙ retraction pp _

    -- 4. Upward closure.
    upward : (c : C) → eⱼ (inclusion c) ≡ eⱼ top
    upward c =
      sym (ap eⱼ (left-top (inclusion c)))
      ∙ respects (sym membership) refl
      ∙ ap eⱼ (absorb-p c)
      ∙ membership

    -- 5. Every unit of C is the unit of truth-point.
    to-truth : (c : C) → eC c ≡ eC truth-point
    to-truth c =
      sym (ap eC (retracts c)) ∙ sym (Tr-η (inclusion c)) ∙ ap Tr (upward c)
      ∙ Tr-η top ∙ ap eC r-top

    -- 6. The Nullstellensatz contracts ʃ sC.
    contractible : Nullstellensatz sC → IsContr (ʃ sC)
    contractible ns = eC truth-point , λ z →
      ns z (eC truth-point ≡ z) (ʃ-set sC _ z) (λ { (box t₀ , e) →
        sym (to-truth (sharp-extract t₀)) ∙ e })
