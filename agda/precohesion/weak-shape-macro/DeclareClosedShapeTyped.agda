{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The explicitly written closed slice (rule C12) with the statement as a
-- NATIVE TYPED ARGUMENT, compared natively with what is declared.
-- Claude (Fable), 14 November 2026; fable-impl-21
-- (FABLE-C12-RECONCILIATION-REQUEST; independent audit, Part A, 4.5 and
-- 5.2; reconciliation-probes C12Inline, C12AsOrdinary, C12AsCrisp,
-- C12NamedAsCrisp).
--
--   unquoteDecl k = declareClosedShapeTyped k (RelativeShapeOver Γ d A)
--
-- declares ONE constant k, and k has the statement AS IT IS WRITTEN.
-- There is no quoteTerm in the call: the statement is an ordinary
-- argument of type Set ℓ, checked by Agda before the program runs.
--
-- WHY THIS MODULE EXISTS. DeclareClosedShape.declareClosedShape takes the
-- statement as REFLECTED SYNTAX and declares the elaboration of that
-- syntax. Reflected syntax has no cohesion annotation: the argument
-- information of Agda.Builtin.Reflection is a visibility, a relevance and
-- a quantity. So a function type with a crisp binder written INLINE in the
-- statement, (@♭ x : B) → C, is read back as (x : B) → C, and where the
-- result still type-checks that entry point declares the constant for the
-- OTHER statement (the family argument of the schema is such a place:
-- nothing else in the statement pins it). What it declares is still a
-- closed, natively checked instance of the schema, and a later use at the
-- intended type is refused; but the constant is not the one that was
-- asked for, and nothing says so at the declaration.
--
-- WHAT THIS ENTRY POINT DOES. It makes the same checks as the earlier one
-- (both reflection flags fixed; the context of the calling declaration
-- and the current context empty; the statement an application of
-- RelativeShapeOver or of ClosedShapeOver, checked in the empty context)
-- and two more, both made by Agda's type checker against the ORIGINAL
-- native statement, which never passes through reflection:
--   * BEFORE the declaring primitive: a placeholder of the type that
--     reflection would declare is checked at the native statement
--     (unquoteTC at the native type). The step is speculative and leaves
--     no trace. If the two types differ, the error is the compiler's own
--     (UnequalTypes), and nothing is declared.
--   * AFTER it: the new constant, with the type that the compiler STORED
--     for it, is checked at the native statement once more. So that the
--     stored type is the written statement is a checked fact of every
--     declaration made here, not an argument.
-- The compiler's error is passed on unchanged, on purpose: it is the one
-- message that shows the two types as they are. The statement cannot be
-- printed faithfully by this program, since printing goes through the
-- same reflected syntax.
--
-- WHAT IS ACCEPTED AND WHAT IS REFUSED.
--   * A statement whose family is given BY NAME (a closed definition) is
--     accepted, whatever binders the definition of the family contains:
--     reflection keeps a name as a name. The constant then also checks at
--     the family written out inline, by ordinary conversion.
--   * A statement with only ordinary function types inline is accepted.
--   * A statement with a crisp function type written INLINE is REFUSED
--     (UnequalTypes: one domain is flat, the other continuous). It is not
--     declared in an altered form. The remedy is the first item: give the
--     family a name. A closed family can always be named.
--
-- THE EARLIER ENTRY POINT IS KEPT, unchanged, as the reflected-term entry
-- point. Its input contract: the term it is given IS the statement; what
-- the term denotes after elaboration is declared; no comparison with a
-- native type is made there. It suits callers that hold syntax (other
-- programs). For a statement written by hand in a source file this module
-- is the one to use.
--
-- `declare` is the only definition of this module that contains a
-- declaring primitive. Every condition of admission is checked in that
-- definition before the primitive is reached, as in DeclareClosedShape;
-- the comparison of the stored type follows it. `private` is a boundary
-- of the source interface, not of reflection (FABLE-REVIEW-03, sections
-- 1.3 and 3).
module DeclareClosedShapeTyped where

open import Foundations using (Level)
open import ClosedSliceShape using (ClosedShapeOver)
open import RelativeSliceShape using (RelativeShapeOver)
open import CaptureExplicit using (guarded)
open import Agda.Builtin.Reflection as R using (Name; Term; TC; Telescope)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Bool using (false)

private
  infixl 1 _>>=_
  _>>=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
  _>>=_ = R.bindTC

  open-context : TC ⊤
  open-context = R.typeError
    (R.strErr "Closed shape declarations cannot depend on native module or local parameters. Package the intended object context as a closed native base and family." ∷ [])

  wrong-head : TC ⊤
  wrong-head = R.typeError
    (R.strErr "Expected a ClosedShapeOver or RelativeShapeOver type." ∷ [])

  -- Checks only: the next four functions declare nothing.
  both-empty : Telescope → Telescope → TC ⊤
  both-empty [] [] = R.returnTC tt
  both-empty _ _ = open-context

  shape-head : Term → TC ⊤
  shape-head (R.def (quote ClosedShapeOver) _) = R.returnTC tt
  shape-head (R.def (quote RelativeShapeOver) _) = R.returnTC tt
  shape-head _ = wrong-head

  -- `reflected` is the statement after its passage through reflection and
  -- a fresh elaboration: the type that declarePostulate is about to store.
  -- A placeholder of that type is checked at the native statement. The
  -- type argument of unquoteTC is the native type itself, not syntax.
  -- runSpeculative with `false` restores the state: the placeholder does
  -- not survive, and no metavariable of the caller is touched.
  as-written : {ℓ : Level} (Statement : Set ℓ) → Term → TC ⊤
  as-written Statement reflected = R.runSpeculative (
    R.checkType R.unknown reflected >>= λ placeholder →
    R.unquoteTC {A = Statement} placeholder >>= λ _ →
    R.returnTC (tt , false))

  -- The same question for the constant as the compiler stored it.
  stored-as-written : {ℓ : Level} (Statement : Set ℓ) → Name → TC ⊤
  stored-as-written Statement n =
    R.unquoteTC {A = Statement} (R.def n []) >>= λ _ → R.returnTC tt

  -- The only definition of this module that contains a declaring
  -- primitive. In this order: flags; both contexts; the head, read off
  -- the reflected statement (a head is a name, and reflection keeps
  -- names); well-formedness in the empty context; the native comparison;
  -- then declarePostulate; then the comparison of the stored type.
  declare : {ℓ : Level} → Name → (Statement : Set ℓ) → TC ⊤
  declare n Statement = guarded (
    R.inContext [] R.getContext >>= λ calling →
    R.getContext >>= λ current →
    both-empty calling current >>= λ _ →
    R.quoteTC Statement >>= λ t →
    shape-head t >>= λ _ →
    R.inferType t >>= λ sort →
    R.checkType t sort >>= λ reflected →
    as-written Statement reflected >>= λ _ →
    R.declarePostulate
      (R.arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω)) n)
      reflected >>= λ _ →
    stored-as-written Statement n)

-- Use: unquoteDecl k = declareClosedShapeTyped k (RelativeShapeOver Γ d A)
--  or: unquoteDecl k = declareClosedShapeTyped k (ClosedShapeOver Γ s d A)
declareClosedShapeTyped : {ℓ : Level} → Name → (Statement : Set ℓ) → TC ⊤
declareClosedShapeTyped = declare
