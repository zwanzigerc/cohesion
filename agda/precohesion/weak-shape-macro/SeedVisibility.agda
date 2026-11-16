{-# OPTIONS --cohesion --without-K --flat-split #-}

-- What an instance search sees of generated names. Claude (Fable),
-- 13 November 2026; generator checkpoint after fable-impl-11. The compiled
-- answer to the question of HANDOFF-23: "test visibility of hidden
-- auxiliary declareShape seeds under a single public unquoteDecl
-- diagram". The probes of parts 1, 2 and 4 are small reflection programs
-- of this file, not the diagram generator; part 3 uses the generator.
--
-- `candidates-at T` is the number of candidates that getInstances returns
-- for a goal of type T, with all search state discarded. Two facts about
-- that primitive matter for reading the numbers:
--   * a candidate must be a name in SCOPE;
--   * the compiler checks candidates against the goal before the
--     reflection primitive sees them, and can collapse candidates that
--     are equal by conversion: it keeps the first checked candidate and
--     drops the candidates directly after it that are equal to it, under
--     its own conditions on blocked comparisons and metas; it does not
--     deduplicate the whole list (InstanceArguments.hs,
--     dropSameCandidates; S2-GETINSTANCES-FILTERING-01). So a count is
--     not a number of registrations. A count of ZERO cannot come from
--     that collapse.
--
-- RESULTS, each a `refl` below.
--   1. A seed declared as an instance under a FRESH name, inside a
--      declaration that does not list it: 0 candidates within the same
--      call after the seed is complete, 0 afterwards. A later ordinary
--      request declares its own axiom (SeedHiddenDistinct.agda.fail).
--      The probe's declaration lists TWO public names, both bookkeeping
--      (a count and a holder); the diagram generator lists one, its
--      bundle. What matters is that the seed's name is not listed.
--   2. Seeds whose names are LISTED in the unquoteDecl: the first is a
--      candidate within the call as soon as it is defined; the second
--      request reuses it; later requests reuse it.
--   3. A public bundle: 1 candidate at the head ClosedDiagram, at top
--      level and inside a module with a crisp parameter; 0 candidates at
--      CapturedShape of its sources, although the lookup of CaptureReuse
--      finds both seeds through the bundle. A bundle instance declared
--      inside a module with a parameter is a candidate inside it.
--   4. A hidden seed OFFERED by name to a later capture of the same call
--      (DeclareCapturedShape.declareSeed) is used. At top level: one
--      axiom for two requests of one source with the offer; two axioms
--      for two requests of another source without it (the control);
--      nothing registered. In a module with a crisp parameter: the
--      offered pair has equal wrappers and equal whole payloads by refl
--      and registers nothing. There is no unoffered control and no
--      rooted count inside the module.
module SeedVisibility where

open import Foundations
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import DeclareCapturedShape using (declareShape; declareSeed)
open import BoolDecidable using (bool-is-set; bool-is-discrete)
open import AssemblyFixtures using (collapse; keep; Colours)
open import DiagramData
open import DeclareDiagram using (declareClosedDiagram)
open import DiagramInventory using (shape-axioms)
open import Agda.Builtin.Reflection
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (_,_)

private
  infixl 1 _>>=_
  _>>=_ = bindTC
  ret = returnTC

  v : {A : Set} → A → Arg A
  v = arg (arg-info visible (modality relevant quantity-ω))

  length : {A : Set} → List A → Nat
  length [] = zero
  length (_ ∷ xs) = suc (length xs)

  candidates : Term → TC (List Term)
  candidates (meta m _) = getInstances m
  candidates _ = ret []

  countAt : Term → TC Nat
  countAt ty = runSpeculative
    (checkType unknown ty >>= candidates >>= λ cs → ret (length cs , false))

macro
  candidates-at : ∀ {a} → Set a → Term → TC ⊤
  candidates-at T hole = quoteTC T >>= countAt >>= λ n → unify hole (lit (nat n))

------------------------------------------------------------------------
-- 1. A hidden auxiliary instance: its name is not among the listed ones.

before : candidates-at (CapturedShape {ℓ = lzero} ⊤) ≡ 0
before = refl

-- `count` records what a search sees WITHIN the call, after the seed has
-- been declared as an instance and defined by declareShape. `held` keeps
-- the hidden seed reachable under a public name that is not an instance.
hidden-seed : Name → Name → TC ⊤
hidden-seed count held =
  freshName "hidden-seed" >>= λ aux →
  declareShape {ℓ = lzero} aux ⊤ >>= λ _ →
  quoteTC (CapturedShape {ℓ = lzero} ⊤) >>= λ ty →
  countAt ty >>= λ n →
  declareDef (v count) (def (quote Nat) []) >>= λ _ →
  defineFun count (clause [] [] (lit (nat n)) ∷ []) >>= λ _ →
  declareDef (v held) ty >>= λ _ →
  defineFun held (clause [] [] (def aux []) ∷ [])

unquoteDecl within held = hidden-seed within held

within-is : within ≡ 0
within-is = refl

after : candidates-at (CapturedShape {ℓ = lzero} ⊤) ≡ 0
after = refl

later : CapturedShape ⊤
later = shape

------------------------------------------------------------------------
-- 2. Seeds named in the declaration.

named-seeds : Name → Name → Name → TC ⊤
named-seeds count seedB seedC =
  declareShape {ℓ = lzero} seedB Bool >>= λ _ →
  quoteTC (CapturedShape {ℓ = lzero} Bool) >>= countAt >>= λ n →
  declareShape {ℓ = lzero} seedC Bool >>= λ _ →
  declareDef (v count) (def (quote Nat) []) >>= λ _ →
  defineFun count (clause [] [] (lit (nat n)) ∷ [])

unquoteDecl seen seedB seedC = named-seeds seen seedB seedC

seen-is : seen ≡ 1
seen-is = refl

one-choice : seedB ≡ seedC
one-choice = refl

-- Two names, equal by conversion: one candidate.
named-after : candidates-at (CapturedShape {ℓ = lzero} Bool) ≡ 1
named-after = refl

named-later : CapturedShape Bool
named-later = shape

named-later-same : named-later ≡ seedB
named-later-same = refl

------------------------------------------------------------------------
-- 3. A public bundle.

no-bundle-yet : candidates-at (ClosedDiagram lzero) ≡ 0
no-bundle-yet = refl

unquoteDecl colours =
  declareClosedDiagram colours
    bool-is-discrete bool-is-set bool-is-discrete bool-is-set collapse Colours

bundle-registered : candidates-at (ClosedDiagram lzero) ≡ 1
bundle-registered = refl

-- Its seeds are not instances of CapturedShape ...
no-direct-seed : candidates-at (CapturedShape {ℓ = lzero} (Σ Bool Colours)) ≡ 0
no-direct-seed = refl

-- ... and are found all the same, through the bundle.
through-bundle : CapturedShape (Σ Bool Colours)
through-bundle = shape

through-bundle-same : through-bundle ≡ ClosedSeed.seedB colours
through-bundle-same = refl

module Inside (@♭ b : Bool) where
  bundle-visible : candidates-at (ClosedDiagram lzero) ≡ 1
  bundle-visible = refl

  -- A bundle instance declared INSIDE the module (hand-written; its
  -- payloads are closed and given) is a candidate there as well: two
  -- candidates, which differ in their maps.
  instance
    inner : ClosedDiagram lzero
    inner = closed-diagram Bool Bool
      bool-is-discrete bool-is-set bool-is-discrete bool-is-set
      keep Colours
      (ClosedField.KB colours) (ClosedField.KB colours)

  both-visible : candidates-at (ClosedDiagram lzero) ≡ 2
  both-visible = refl

------------------------------------------------------------------------
-- 4. Offering a completed hidden seed by name.

-- Two hidden seeds for one source, bound to two public names that are not
-- instances. `offer` says whether the second capture is offered the first.
two-seeds : Bool → Name → Name → (@♭ X : Set) → TC ⊤
two-seeds offer left right X =
  freshName "left-seed" >>= λ sl →
  declareSeed {ℓ = lzero} [] sl X >>= λ _ →
  freshName "right-seed" >>= λ sr →
  declareSeed {ℓ = lzero} (offered offer sl) sr X >>= λ _ →
  quoteTC (CapturedShape {ℓ = lzero} X) >>= λ ty →
  declareDef (v left) ty >>= λ _ →
  defineFun left (clause [] [] (def sl []) ∷ []) >>= λ _ →
  declareDef (v right) ty >>= λ _ →
  defineFun right (clause [] [] (def sr []) ∷ [])
  where
  offered : Bool → Name → List Term
  offered true s = def s [] ∷ []
  offered false _ = []

unquoteDecl shared-left shared-right =
  two-seeds true shared-left shared-right (Bool → Bool)

shared : shared-left ≡ shared-right
shared = refl

shared-axioms : shape-axioms [] (quote shared-left ∷ quote shared-right ∷ []) ≡ 1
shared-axioms = refl

unquoteDecl apart-left apart-right =
  two-seeds false apart-left apart-right (Bool → Bool → Bool)

apart-axioms : shape-axioms [] (quote apart-left ∷ quote apart-right ∷ []) ≡ 2
apart-axioms = refl

-- Neither pair registered anything.
nothing-registered : candidates-at (CapturedShape {ℓ = lzero} (Bool → Bool)) ≡ 0
nothing-registered = refl

-- The same in a module with a crisp parameter: the seeds are contextual
-- choices, declared in the context of the call, and the offered term is
-- the first seed's name as written in that context.
module Offered (@♭ b : Bool) where

  unquoteDecl left right = two-seeds true left right (Colours b)

  offered-choice : left ≡ right
  offered-choice = refl

  same-payload : C.Output.whole-context left ≡ C.Output.whole-context right
  same-payload = refl

  not-registered : candidates-at (CapturedShape {ℓ = lzero} (Colours b)) ≡ 0
  not-registered = refl
