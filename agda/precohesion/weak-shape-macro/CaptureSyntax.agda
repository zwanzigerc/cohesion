{-# OPTIONS --cohesion --without-K #-}

-- Reflected syntax operations used before introducing any captured axiom.
-- `requireClosed` checks de Bruijn closure only. A caller must ALSO audit
-- names: Agda can omit implicit surrounding module arguments on local names.
module CaptureSyntax where

open import Agda.Builtin.Reflection as R using (Term; Sort; Arg; Abs; Clause; Pattern; TC)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _<_)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)

private
  infixl 1 _>>=_
  _>>=_ = R.bindTC
  return = R.returnTC

  fail : {A : Set} → String → TC A
  fail message = R.typeError (R.strErr message ∷ [])

  length : {A : Set} → List A → Nat
  length [] = zero
  length (_ ∷ xs) = suc (length xs)

  shiftIndex : Nat → Nat → Nat → Nat
  shiftIndex amount cutoff index with index < cutoff
  ... | true = index
  ... | false = amount + index

mutual
  -- Insert `amount` binders at de Bruijn `cutoff`.
  shift : Nat → Nat → Term → Term
  shift amount cutoff (R.var index args) =
    R.var (shiftIndex amount cutoff index) (shiftArgs amount cutoff args)
  shift amount cutoff (R.con name args) = R.con name (shiftArgs amount cutoff args)
  shift amount cutoff (R.def name args) = R.def name (shiftArgs amount cutoff args)
  shift amount cutoff (R.lam visibility (R.abs name body)) =
    R.lam visibility (R.abs name (shift amount (suc cutoff) body))
  shift amount cutoff (R.pi (R.arg info domain) (R.abs name body)) =
    R.pi (R.arg info (shift amount cutoff domain))
      (R.abs name (shift amount (suc cutoff) body))
  shift amount cutoff (R.pat-lam clauses args) =
    R.pat-lam (shiftClauses amount cutoff clauses) (shiftArgs amount cutoff args)
  shift amount cutoff (R.agda-sort sort) = R.agda-sort (shiftSort amount cutoff sort)
  shift amount cutoff (R.lit literal) = R.lit literal
  shift amount cutoff (R.meta meta args) = R.meta meta (shiftArgs amount cutoff args)
  shift amount cutoff R.unknown = R.unknown

  shiftSort : Nat → Nat → Sort → Sort
  shiftSort amount cutoff (R.set level) = R.set (shift amount cutoff level)
  shiftSort amount cutoff (R.prop level) = R.prop (shift amount cutoff level)
  shiftSort _ _ (R.lit level) = R.lit level
  shiftSort _ _ (R.propLit level) = R.propLit level
  shiftSort _ _ (R.inf level) = R.inf level
  shiftSort _ _ R.unknown = R.unknown

  shiftArgs : Nat → Nat → List (Arg Term) → List (Arg Term)
  shiftArgs amount cutoff [] = []
  shiftArgs amount cutoff (R.arg info value ∷ values) =
    R.arg info (shift amount cutoff value) ∷ shiftArgs amount cutoff values

  shiftTelescope : Nat → Nat → R.Telescope → R.Telescope
  shiftTelescope amount cutoff [] = []
  shiftTelescope amount cutoff ((name , R.arg info domain) ∷ rest) =
    (name , R.arg info (shift amount cutoff domain))
      ∷ shiftTelescope amount (suc cutoff) rest

  shiftPattern : Nat → Nat → Pattern → Pattern
  shiftPattern amount cutoff (R.con name patterns) =
    R.con name (shiftPatterns amount cutoff patterns)
  shiftPattern amount cutoff (R.dot term) = R.dot (shift amount cutoff term)
  -- Pattern variables refer to their clause telescope, rather than to free
  -- variables of the surrounding term, so these indices stay fixed.
  shiftPattern _ _ (R.var index) = R.var index
  shiftPattern _ _ (R.lit literal) = R.lit literal
  shiftPattern _ _ (R.proj name) = R.proj name
  shiftPattern _ _ (R.absurd index) = R.absurd index

  shiftPatterns : Nat → Nat → List (Arg Pattern) → List (Arg Pattern)
  shiftPatterns _ _ [] = []
  shiftPatterns amount cutoff (R.arg info pat ∷ patterns) =
    R.arg info (shiftPattern amount cutoff pat)
      ∷ shiftPatterns amount cutoff patterns

  shiftClause : Nat → Nat → Clause → Clause
  shiftClause amount cutoff (R.clause telescope patterns body) =
    R.clause (shiftTelescope amount cutoff telescope)
      (shiftPatterns amount (length telescope + cutoff) patterns)
      (shift amount (length telescope + cutoff) body)
  shiftClause amount cutoff (R.absurd-clause telescope patterns) =
    R.absurd-clause (shiftTelescope amount cutoff telescope)
      (shiftPatterns amount (length telescope + cutoff) patterns)

  shiftClauses : Nat → Nat → List Clause → List Clause
  shiftClauses _ _ [] = []
  shiftClauses amount cutoff (cl ∷ clauses) =
    shiftClause amount cutoff cl ∷ shiftClauses amount cutoff clauses

mutual
  -- Remove the newest `count` variables of the OUTER context. Bound
  -- variables introduced inside the term are preserved. Refuse any actual
  -- use of a removed variable, or syntax whose dependencies are unresolved.
  dropUnder : Nat → Nat → Term → TC Term
  dropUnder count depth (R.var index args) with index < depth
  ... | true = dropArgs count depth args >>= λ args' → return (R.var index args')
  ... | false with index < (depth + count)
  ...   | true = fail "Context capture cannot discard a variable used by this type."
  ...   | false = dropArgs count depth args >>= λ args' → return (R.var (index - count) args')
  dropUnder count depth (R.con name args) =
    dropArgs count depth args >>= λ args' → return (R.con name args')
  dropUnder count depth (R.def name args) =
    dropArgs count depth args >>= λ args' → return (R.def name args')
  dropUnder count depth (R.lam visibility (R.abs name body)) =
    dropUnder count (suc depth) body >>= λ body' →
    return (R.lam visibility (R.abs name body'))
  dropUnder count depth (R.pi (R.arg info domain) (R.abs name body)) =
    dropUnder count depth domain >>= λ domain' →
    dropUnder count (suc depth) body >>= λ body' →
    return (R.pi (R.arg info domain') (R.abs name body'))
  dropUnder count depth (R.agda-sort sort) =
    dropSort count depth sort >>= λ sort' → return (R.agda-sort sort')
  dropUnder _ _ (R.lit literal) = return (R.lit literal)
  dropUnder _ _ (R.pat-lam _ _) =
    fail "Context capture does not yet support extended pattern lambdas; use a globally defined family."
  dropUnder _ _ (R.meta _ _) =
    fail "Context capture requires solved metavariables before closing a type."
  dropUnder _ _ R.unknown =
    fail "Context capture cannot close an unknown reflected term."

  dropArgs : Nat → Nat → List (Arg Term) → TC (List (Arg Term))
  dropArgs _ _ [] = return []
  dropArgs count depth (R.arg info value ∷ values) =
    dropUnder count depth value >>= λ value' →
    dropArgs count depth values >>= λ values' →
    return (R.arg info value' ∷ values')

  dropSort : Nat → Nat → Sort → TC Sort
  dropSort count depth (R.set level) =
    dropUnder count depth level >>= λ level' → return (R.set level')
  dropSort count depth (R.prop level) =
    dropUnder count depth level >>= λ level' → return (R.prop level')
  dropSort _ _ (R.lit level) = return (R.lit level)
  dropSort _ _ (R.propLit level) = return (R.propLit level)
  dropSort _ _ (R.inf level) = return (R.inf level)
  dropSort _ _ R.unknown = fail "Context capture cannot close an unknown universe sort."

dropNewest : Nat → Term → TC Term
dropNewest count = dropUnder count zero

mutual
  closedUnder : Nat → Term → TC ⊤
  closedUnder depth (R.var index args) with index < depth
  ... | true = closedArgs depth args
  ... | false = fail "Captured declaration still contains a free native variable."
  closedUnder depth (R.con _ args) = closedArgs depth args
  closedUnder depth (R.def _ args) = closedArgs depth args
  closedUnder depth (R.lam _ (R.abs _ body)) = closedUnder (suc depth) body
  closedUnder depth (R.pi (R.arg _ domain) (R.abs _ body)) =
    closedUnder depth domain >>= λ _ → closedUnder (suc depth) body
  closedUnder depth (R.agda-sort sort) = closedSort depth sort
  closedUnder _ (R.lit _) = return tt
  closedUnder _ (R.meta _ _) =
    fail "Captured declaration contains an unresolved metavariable."
  closedUnder _ R.unknown = fail "Captured declaration contains unknown reflected syntax."
  closedUnder _ (R.pat-lam _ _) =
    fail "Context capture does not yet support extended pattern lambdas; use a globally defined family."

  closedArgs : Nat → List (Arg Term) → TC ⊤
  closedArgs _ [] = return tt
  closedArgs depth (R.arg _ value ∷ values) =
    closedUnder depth value >>= λ _ → closedArgs depth values

  closedSort : Nat → Sort → TC ⊤
  closedSort depth (R.set level) = closedUnder depth level
  closedSort depth (R.prop level) = closedUnder depth level
  closedSort _ (R.lit _) = return tt
  closedSort _ (R.propLit _) = return tt
  closedSort _ (R.inf _) = return tt
  closedSort _ R.unknown = fail "Captured declaration contains an unknown universe sort."

-- This deliberately does not claim to detect hidden module parameters on
-- `def`/`con` names. The capture frontend must reject/expand those separately.
requireClosed : Term → TC ⊤
requireClosed = closedUnder zero
