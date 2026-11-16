{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Automatic whole-context capture. The typed term-macro interface is
-- intentional: its final unification checks against the ORIGINAL native
-- source type, including cohesion information absent from reflected syntax.
--
-- 11 November 2026, Fable overlay on bundle v4 (FABLE-ADDITIONS.txt):
-- earlier generated shapes of the same file are admitted by counting their
-- hidden parameters (LocalPolicy, admitLocal); shape-in-module is new.
--
-- 12 November 2026, fable-impl-01 (FABLE-IMPL-01.txt): this module no longer
-- calls Agda's parameter reconstruction at all. Dropped parameters are made
-- explicit by CaptureExplicit, through ordinary elaboration.
--
-- 13 November 2026, fable-impl-02 (FABLE-IMPL-02.txt): every entry point
-- runs with reconstruction and normalisation switched off (`guarded`); the
-- native arity of a generated axiom is recorded in its name when it is
-- declared, and an earlier axiom is admitted on that record only.
--
-- 13 November 2026, fable-impl-03 (FABLE-IMPL-03.txt, FABLE-REVIEW-03.txt
-- section 2): the record now also says whether the axiom was declared
-- through hidden parameters, and an occurrence is judged by the number of
-- arguments it shows. The closure of the default macro no longer depends on
-- how Agda computes the number of hidden arguments (ancestor sections,
-- let-bound modules, refined parameters), nor on reading the type of an
-- earlier axiom from another position. Internal helpers are private.
--
-- 13 November 2026, fable-impl-04 (FABLE-IMPL-04.txt, FABLE-REVIEW-03.txt
-- section 2): every generated axiom takes one further argument of the unit
-- type, after the variables of its context. An occurrence that shows all
-- its arguments then hides none for every arity, including zero. Both
-- macros refuse an occurrence that shows none of its arguments. The two
-- internal errors that fable-impl-03 still reached through recorded axioms
-- (RefinedConstantAbort, RefinedHiddenAbort) were occurrences of that kind
-- and are reported errors now. The explanation below is corrected in the
-- two places named by FRONTEND-M3-AUDIT-01, section 2.
--
-- 13 November 2026, fable-impl-05 (FABLE-IMPL-05.txt; FRONTEND-M4-AUDIT-01
-- section 4): comments and one message only, no change of behaviour. Four
-- statements of fable-impl-04 about the occurrence that shows no argument
-- said more than is proved. They are restated with their conditions: the
-- refusal is a conservative rule, and its relation to the compiler's
-- internal error holds for occurrences with all their arguments, under
-- the two conditions given in rule 2 below.
--
-- 13 November 2026, fable-impl-07 (FABLE-IMPL-07.txt; FABLE03-FRONTEND-
-- RECONCILIATION-01 section 2): one comment only, no change of behaviour.
-- The paragraph on the default macro said that every argument of an
-- admitted axiom is a closed term. What the audit establishes is that the
-- WHOLE payload has no free variable of the context of the call; an
-- argument may contain variables bound inside the payload (CaptureNested).
--
-- 13 November 2026, step S3b after fable-impl-13 (HANDOFF-30;
-- S3-PACKED-DATA-AUDIT-SEAM-01): PREPARATION WITHOUT DECLARATION. The
-- capture is cut into the pieces it already consisted of (the site of the
-- call, the source, the telescope, the audited payload, the commit), in
-- the same order, with the same primitives; the macros behave as before.
-- A generator that packs further data over the same context needs the
-- same name policy, the same exposure of source-local names, the same
-- recovery of dropped parameters and the same closure audit. They are
-- exported at the end of this module as guarded programs that look
-- nothing up and declare nothing (`frame` and the programs that take a
-- Frame). The passes themselves stay private: there is one auditor.
module CaptureShape where

open import Foundations using (lzero; lsuc)
open import CaptureContext
open import CapturedShape using (CapturedShape; captured)
open import RelativeSliceShape using (RelativeShapeOver)
open import CaptureCrispCheck using (checkCrispContext)
open import CaptureSyntax using (shift; dropNewest; requireClosed)
open import CaptureReuse using (findShapeOffering)
open import CaptureExplicit using (explicit; guarded)
open import Agda.Builtin.Reflection as R
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_; _<_; _==_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String; primStringToList; primStringAppend; primShowNat)
open import Agda.Builtin.Char using (Char; primCharEquality; primCharToNat)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)

private
  infixl 1 _>>=_
  _>>=_ = bindTC
  ret = returnTC

  v : {A : Set} → A → Arg A
  v = arg (arg-info visible (modality relevant quantity-ω))
  h : {A : Set} → A → Arg A
  h = arg (arg-info hidden (modality relevant quantity-ω))

  fail : {A : Set} → String → TC A
  fail s = typeError (strErr s ∷ [])

  length : {A : Set} → List A → Nat
  length [] = zero
  length (_ ∷ xs) = suc (length xs)

  reverseOnto : {A : Set} → List A → List A → List A
  reverseOnto [] ys = ys
  reverseOnto (x ∷ xs) ys = reverseOnto xs (x ∷ ys)

  append : {A : Set} → List A → List A → List A
  append [] ys = ys
  append (x ∷ xs) ys = x ∷ append xs ys

  maximum : Nat → Nat → Nat
  maximum a b with a < b
  ... | true = b
  ... | false = a

  level : Nat → Term
  level zero = def (quote lzero) []
  level (suc n) = def (quote lsuc) (v (level n) ∷ [])

  rootPrefix : List Char → List Char
  rootPrefix [] = []
  rootPrefix (c ∷ cs) with primCharEquality c '.'
  ... | true = '.' ∷ []
  ... | false = c ∷ rootPrefix cs

  prefixOf : List Char → List Char → Bool
  prefixOf [] _ = true
  prefixOf (_ ∷ _) [] = false
  prefixOf (x ∷ xs) (y ∷ ys) with primCharEquality x y
  ... | true = prefixOf xs ys
  ... | false = false

  localName : List Char → Name → Bool
  localName [] _ = false
  localName prefix n = prefixOf prefix (primStringToList (primShowQName n))

-- Source-local names in a captured type.
--
-- Reflected syntax leaves out the first n arguments of every name x, where
-- n = n(x, p) depends on x and on the position p of the macro call only;
-- elaboration of reflected syntax puts n arguments back, and getType
-- instantiates the first n binders. In Agda 2.9.0-rc3,
--   n(x, p) = (variables of let-bound modules that x lies under)
--           + (parameters of the module section shared by x and p)
-- (Signature.hs getModuleFreeVars, Env.hs getAnonymousVariables). Nothing
-- below uses this formula. What is used is that ONE number governs quoting
-- and elaboration during one expansion, and the following two rules.
--
-- 1. A source-local name is admitted only if it is an axiom declared by an
--    earlier expansion of this macro. Such an axiom K has the native type
--      K : (x1 ... xT) -> ⊤ ->
--          RelativeShapeOver <context> <discreteness> <family>
--    where x1 ... xT is the WHOLE context of the expansion that declared
--    it (Agda abstracts every declared constant over that context), and
--    the unit argument is added by this module: every generated axiom
--    takes at least one argument, and the wrapper applies it to tt. T is
--    recorded when K is declared, in the name of K:
--      contextual-shape (T)   every recorded axiom in the audited payload
--                             of K showed all its arguments; or T = 0, the
--                             context was empty, and nothing was audited;
--      ambient-shape (T)      K was declared by shape-in-module and its
--                             audited payload contains a recorded axiom
--                             that did not show all its arguments.
--    T is the length of  inContext [] getContext , the context of the macro
--    call itself. A name with a space and parentheses cannot be written in
--    an Agda source file and is never in scope; so a hand-written
--    declaration never has this form, and no module application copies it.
--    Every other source-local name is refused: a transparent definition
--    has been unfolded before the audit, and what remains (postulates,
--    data and record types, abstract or opaque definitions, and copies of
--    such names made by a module application) can hide arguments which no
--    reflection primitive shows.
--
-- 2. An occurrence  K a1 ... ak  of a recorded axiom is judged by k alone.
--    K takes exactly T + 1 arguments, a native occurrence has k' <= T + 1
--    of them, and quoting leaves out the first min(n, k'):
--      k = k' - min(n, k').
--    k = T + 1  Then k' = T + 1 and n = 0: nothing is hidden. The
--               occurrence is written out in full in the audited term and
--               is elaborated back without any inserted argument. Because
--               T + 1 >= 1 this holds for every T, also for T = 0.
--    1 <= k <= T  Not all arguments are shown: some are hidden, or the
--               occurrence is partially applied; the two are treated
--               alike. In either case n < k' <= T + 1, so n <= T. Nothing
--               is assumed about WHICH arguments are hidden. They are the
--               first n, and after a with-abstraction or a refinement
--               these are not the parameters of the enclosing module, so
--               what Agda puts back for them can be wrong (CaptureWith
--               section 4, CaptureRefinedMismatch). The default macro
--               never lets Agda put anything back.
--    k = 0      Nothing is shown. For an occurrence with all its
--               arguments this means n >= T + 1: more arguments are hidden
--               than K has context variables. If moreover
--                 (i)  the section of the module of K has exactly T
--                      entries, which is so when the declaring expansion
--                      ran in a fresh module or with an identity
--                      parameter substitution, and
--                 (ii) a parameter substitution for that module is
--                      available at the present position,
--               then 2.9.0-rc3 stops with an internal error
--               (Signature.hs:1480) when the name is elaborated here.
--               Without (ii) Agda inserts no argument and does not stop
--               there (Signature.hs:1466). The known instances are axioms
--               declared in a clause that refines module parameters and
--               mentioned from a sibling clause. An occurrence applied to
--               no argument at all shows none either. Both macros refuse
--               k = 0 in every case. This is a conservative rule, applied
--               during the audit: before the audit calls getDefinition or
--               getType on the name, and before the audited term is
--               elaborated again. It does not come before the first
--               elaboration of an expansion, which is of the types that
--               Agda supplies for the hole and for the context variables.
--
-- explicit-only  (macro `shape`, declareShape) admits a contextual axiom at
--   k = T + 1 and nothing else. In a non-empty context the audited payload
--   has no FREE variable, that is, none of the context of the call
--   (requireClosed counts binders and accepts a variable exactly when it
--   is bound inside the term). Every admitted axiom occurs in it with all
--   its arguments written out. Such an argument need not be a closed term
--   by itself: it may contain variables bound by a λ or a Π of the payload
--   (CaptureNested applies an earlier axiom to one), and it contains none
--   of the context of the call. The declared payload is that term: it is
--   closed as a whole, and the new axiom is again contextual. In an empty
--   context nothing is audited and the payload is closed because the
--   context is empty (FABLE-REVIEW-03.txt, Theorem 2.3, as restated in
--   FABLE-REVIEW-05.txt section 1).
-- ambient-too    (macro `shape-in-module`) also admits recorded axioms at
--   1 <= k <= T. Agda puts hidden arguments back when the payload is
--   declared (without stopping, under conditions (i) and (ii) of rule 2;
--   that they are the arguments that were dropped is NOT proved, and after
--   a refinement or a with-abstraction they are not, see rule 2); the
--   payload then mentions the earlier axiom at parameters of the
--   surrounding module, and the new axiom is recorded as ambient. No
--   macro admits an ambient axiom at k = T + 1, that is from outside the
--   module whose parameters it was taken at.
--
-- What this does and does not establish. The record is a record, not
-- provenance: a reflection program other than this frontend can call
-- freshName with a reserved form and declare an axiom under a wrong record
-- (diagnostics/ForgedByReflection.agda). Nothing in Agda's reflection
-- interface distinguishes the author of a declaration. The statements above
-- are for files in which every recorded name was declared by an execution
-- of an exported entry point of this module (captureCore, capture, the two
-- macros, or declareShape through captureCore), with its checks intact. A
-- program that extracts a private function of this module by reflection
-- and calls it is not such an execution. "This module" means this version
-- of it: the reserved form of the name is the same as in fable-impl-03,
-- where a generated axiom has no unit argument, so a tree is rebuilt as a
-- whole when this module changes, and the statements are for files all of
-- whose recorded axioms were declared by the same version. The rules decide what is
-- DECLARED; they do not make every expansion end in a declaration or a
-- reported error: a type handed over by Agda that already mentions a
-- name of a sibling refined clause cannot be elaborated by any reflection
-- program (diagnostics/RefinedNoFrontend.agda).
data LocalPolicy : Set where
  explicit-only ambient-too : LocalPolicy

private
  _and_ : Bool → Bool → Bool
  true and b = b
  false and _ = false

  _or′_ : Bool → Bool → Bool
  true or′ _ = true
  false or′ b = b

  data Kind : Set where
    contextual ambient : Kind

  stem : Kind → String
  stem contextual = "contextual-shape ("
  stem ambient = "ambient-shape ("

  -- The reserved name of an axiom declared in a context of t variables.
  generatedName : Kind → Nat → String
  generatedName k t =
    primStringAppend (stem k) (primStringAppend (primShowNat t) ")")

  -- The last component of a qualified name starts after a dot.
  reversedStem : Kind → List Char
  reversedStem k =
    reverseOnto (primStringToList (primStringAppend "." (stem k))) []

  digit : Char → Maybe Nat
  digit c with primCharToNat c
  ... | k with (k < 48) or′ (57 < k)
  ...   | true = nothing
  ...   | false = just (k - 48)

  whichStem : List Char → Maybe Kind
  whichStem cs with prefixOf (reversedStem contextual) cs
  ... | true = just contextual
  ... | false with prefixOf (reversedStem ambient) cs
  ...   | true = just ambient
  ...   | false = nothing

  withArity : Nat → Maybe Kind → Maybe (Σ Kind (λ _ → Nat))
  withArity t (just k) = just (k , t)
  withArity t nothing = nothing

  -- Decimal digits, least significant first, up to a reserved stem.
  digits : Bool → Nat → Nat → List Char → Maybe (Σ Kind (λ _ → Nat))
  digits some place acc [] = nothing
  digits some place acc (c ∷ cs) with digit c
  ... | just d = digits true (place * 10) (acc + d * place) cs
  ... | nothing with some
  ...   | true = withArity acc (whichStem (c ∷ cs))
  ...   | false = nothing

  closing : List Char → Maybe (Σ Kind (λ _ → Nat))
  closing [] = nothing
  closing (c ∷ cs) with primCharEquality c ')'
  ... | true = digits false 1 zero cs
  ... | false = nothing

  -- The record of a generated axiom; nothing for every name that does not
  -- have a reserved form.
  recorded : Name → Maybe (Σ Kind (λ _ → Nat))
  recorded n = closing (reverseOnto (primStringToList (primShowQName n)) [])

  stripPi : Nat → Term → Σ Nat (λ _ → Term)
  stripPi k (pi _ (abs _ b)) = stripPi (suc k) b
  stripPi k t = k , t

  -- No de Bruijn variable escapes the term. Placeholders for dropped
  -- constructor parameters are tolerated: nothing is re-elaborated from here.
  mutual
    varFree : Nat → Term → Bool
    varFree d (var i args) = (i < d) and varFreeArgs d args
    varFree d (con _ args) = varFreeArgs d args
    varFree d (def _ args) = varFreeArgs d args
    varFree d (lam _ (abs _ t)) = varFree (suc d) t
    varFree d (pi (arg _ a) (abs _ b)) = varFree d a and varFree (suc d) b
    varFree d (agda-sort (set l)) = varFree d l
    varFree d (agda-sort (prop l)) = varFree d l
    varFree d (agda-sort _) = true
    varFree d (lit _) = true
    varFree d unknown = true
    varFree d (meta _ _) = false
    varFree d (pat-lam _ _) = false

    varFreeArgs : Nat → List (Arg Term) → Bool
    varFreeArgs d [] = true
    varFreeArgs d (arg _ t ∷ ts) = varFree d t and varFreeArgs d ts

  -- How many arguments an occurrence shows, of the T + 1 that a recorded
  -- axiom takes: the T variables of its context and the unit argument.
  --   all-shown   T + 1         no parameter is hidden (n = 0)
  --   some-shown  1 .. T        at most T leading arguments are missing
  --   none-shown  0             nothing is shown. If the occurrence has all
  --                             its arguments, T + 1 or more are hidden;
  --                             `reach` does not check that it has.
  data Reach : Set where
    all-shown some-shown none-shown too-many : Reach

  reach : Nat → Nat → Reach
  reach zero total = none-shown
  reach shown@(suc _) total with shown == suc total | shown < suc total
  ... | true | _ = all-shown
  ... | false | true = some-shown
  ... | false | false = too-many

  opaqueLocal : {A : Set} → TC A
  opaqueLocal = fail "Automatic shape capture cannot close an opaque source-local declaration; move it to an imported module or make it an explicit crisp parameter."

  hiddenShape : {A : Set} → TC A
  hiddenShape = fail "Automatic shape capture met an earlier shape that is reached through parameters of the surrounding module or definition, so it cannot be taken at the captured variables. State both shapes as functions of their crisp context (S x = shape), or put the earlier one in a sibling module. The macro shape-in-module accepts this form where the hidden arguments are the parameters of the surrounding module; where a clause or a with-abstraction has refined or reordered them, use the earlier shape at explicit arguments."

  openShape : {A : Set} → TC A
  openShape = fail "Automatic shape capture met an earlier shape whose own declaration is not closed: it was formed by shape-in-module at parameters of its module, and is taken here at explicit arguments. Neither shape nor shape-in-module builds on it from outside that module."

  refinedShape : {A : Set} → TC A
  refinedShape = fail "Automatic shape capture met an earlier shape none of whose arguments is visible here, and refuses it as a precaution. In the known cases the earlier shape was declared in a clause that has refined parameters of this module and is reached through parameters that Agda 2.9.0-rc3 cannot put back from the present clause; an earlier shape applied to no argument at all is refused in the same way. State the earlier shape as a function of its crisp context (S x = shape) and use it at explicit arguments, or use it from outside the module."

  disagrees : {A : Set} → TC A
  disagrees = fail "Automatic shape capture met a declaration whose recorded form does not agree with its type; it was not declared by this frontend."

  -- The record against the declaration. Used only for an occurrence that
  -- shows all T + 1 arguments: then n = 0, no binder of the type is
  -- instantiated by getType, and the type is seen as it was declared, with
  -- its T context binders and the unit binder. A consistency check; the
  -- closure argument does not depend on it.
  checkRecord : Nat → Σ Nat (λ _ → Term) → TC ⊤
  checkRecord total (shown , body@(def (quote RelativeShapeOver) _))
    with (shown == suc total) and varFree zero body
  ... | true = ret tt
  ... | false = disagrees
  checkRecord _ _ = disagrees

  agrees : Nat → Name → TC ⊤
  agrees total n = getDefinition n >>= λ where
    axiom → getType n >>= λ T → checkRecord total (stripPi zero T)
    _ → disagrees

  admit : LocalPolicy → Kind → Reach → Nat → Name → TC ⊤
  admit _ contextual all-shown total n = agrees total n
  admit _ ambient all-shown _ _ = openShape
  admit explicit-only _ some-shown _ _ = hiddenShape
  admit ambient-too _ some-shown _ _ = ret tt
  admit _ _ none-shown _ _ = refinedShape
  admit _ _ too-many _ _ = opaqueLocal

  -- `shown` is the number of arguments of the occurrence being audited.
  admitLocal : LocalPolicy → Name → Nat → TC ⊤
  admitLocal policy n shown with recorded n
  ... | nothing = opaqueLocal
  ... | just (kind , total) = admit policy kind (reach shown total) total n

  mutual
    -- `lenient` keeps the placeholders that plain quoting leaves for dropped
    -- parameters. Only `sanitize` uses it, for the first of its two audits;
    -- everything that leaves `sanitize` has passed the strict audit as well.
    clean : Nat → Bool → LocalPolicy → List Char → Term → TC Term
    clean zero _ _ _ _ = fail "Context capture exceeded its syntax-normalization limit."
    clean (suc fuel) lenient policy prefix (def n args) with localName prefix n
    ... | false = cleanArgs fuel lenient policy prefix args >>= λ as → ret (def n as)
    ... | true = admitLocal policy n (length args) >>= λ _ →
                 cleanArgs fuel lenient policy prefix args >>= λ as → ret (def n as)
    clean (suc fuel) lenient policy prefix (con n args) with localName prefix n
    ... | false = cleanArgs fuel lenient policy prefix args >>= λ as → ret (con n as)
    ... | true = opaqueLocal
    clean (suc fuel) lenient policy prefix (var i args) =
      cleanArgs fuel lenient policy prefix args >>= λ as → ret (var i as)
    clean (suc fuel) lenient policy prefix (lam vis (abs nm body)) =
      clean fuel lenient policy prefix body >>= λ b → ret (lam vis (abs nm b))
    clean (suc fuel) lenient policy prefix (pi (arg info domain) (abs nm body)) =
      clean fuel lenient policy prefix domain >>= λ a →
      clean fuel lenient policy prefix body >>= λ b →
      ret (pi (arg info a) (abs nm b))
    clean (suc fuel) lenient policy prefix (agda-sort (set l)) =
      clean fuel lenient policy prefix l >>= λ l' → ret (agda-sort (set l'))
    clean (suc fuel) lenient policy prefix (agda-sort (prop l)) =
      clean fuel lenient policy prefix l >>= λ l' → ret (agda-sort (prop l'))
    clean (suc fuel) _ _ _ t@(agda-sort _) = ret t
    clean (suc fuel) _ _ _ t@(lit _) = ret t
    clean (suc fuel) _ _ _ (meta _ _) =
      fail "Automatic shape capture requires a fully determined source and context."
    clean (suc fuel) true _ _ unknown = ret unknown
    clean (suc fuel) false _ _ unknown = fail "Automatic shape capture cannot use unknown syntax."
    clean (suc fuel) _ _ _ (pat-lam _ _) =
      fail "Automatic shape capture does not yet support pattern-lambda types."

    cleanArgs : Nat → Bool → LocalPolicy → List Char → List (Arg Term) → TC (List (Arg Term))
    cleanArgs _ _ _ _ [] = ret []
    cleanArgs fuel lenient policy prefix (arg info t ∷ ts) =
      clean fuel lenient policy prefix t >>= λ t' →
      cleanArgs fuel lenient policy prefix ts >>= λ ts' →
      ret (arg info t' ∷ ts')

  _or_ : Bool → Bool → Bool
  true or _ = true
  false or b = b

  mutual
    hasLocal : List Char → Term → Bool
    hasLocal prefix (def n args) = localName prefix n or localArgs prefix args
    hasLocal prefix (con n args) = localName prefix n or localArgs prefix args
    hasLocal prefix (var _ args) = localArgs prefix args
    hasLocal prefix (lam _ (abs _ t)) = hasLocal prefix t
    hasLocal prefix (pi (arg _ a) (abs _ b)) = hasLocal prefix a or hasLocal prefix b
    hasLocal prefix (agda-sort (set l)) = hasLocal prefix l
    hasLocal prefix (agda-sort (prop l)) = hasLocal prefix l
    hasLocal _ _ = false

    localArgs : List Char → List (Arg Term) → Bool
    localArgs _ [] = false
    localArgs prefix (arg _ t ∷ ts) = hasLocal prefix t or localArgs prefix ts

  mutual
    hasUnknown : Term → Bool
    hasUnknown unknown = true
    hasUnknown (def _ args) = unknownArgs args
    hasUnknown (con _ args) = unknownArgs args
    hasUnknown (var _ args) = unknownArgs args
    hasUnknown (lam _ (abs _ t)) = hasUnknown t
    hasUnknown (pi (arg _ a) (abs _ b)) = hasUnknown a or hasUnknown b
    hasUnknown (agda-sort (set l)) = hasUnknown l
    hasUnknown (agda-sort (prop l)) = hasUnknown l
    hasUnknown _ = false

    unknownArgs : List (Arg Term) → Bool
    unknownArgs [] = false
    unknownArgs (arg _ t ∷ ts) = hasUnknown t or unknownArgs ts

  -- Does an audited payload contain a recorded axiom that does not show
  -- all its T + 1 arguments? Then the axiom declared for it is recorded as
  -- ambient. Under explicit-only the audit has refused every such
  -- occurrence already.
  hiddenAt : List Char → Name → Nat → Bool
  hiddenAt prefix n shown with localName prefix n | recorded n
  ... | true | just (_ , total) = shown < suc total
  ... | _ | _ = false

  mutual
    reachesHidden : List Char → Term → Bool
    reachesHidden prefix (def n args) =
      hiddenAt prefix n (length args) or hiddenArgs prefix args
    reachesHidden prefix (con _ args) = hiddenArgs prefix args
    reachesHidden prefix (var _ args) = hiddenArgs prefix args
    reachesHidden prefix (lam _ (abs _ t)) = reachesHidden prefix t
    reachesHidden prefix (pi (arg _ a) (abs _ b)) =
      reachesHidden prefix a or reachesHidden prefix b
    reachesHidden prefix (agda-sort (set l)) = reachesHidden prefix l
    reachesHidden prefix (agda-sort (prop l)) = reachesHidden prefix l
    reachesHidden _ _ = false

    hiddenArgs : List Char → List (Arg Term) → Bool
    hiddenArgs _ [] = false
    hiddenArgs prefix (arg _ t ∷ ts) =
      reachesHidden prefix t or hiddenArgs prefix ts

  kindOf : List Char → Term → Kind
  kindOf prefix payload with reachesHidden prefix payload
  ... | true = ambient
  ... | false = contextual

  -- Reduce whole terms only, in their actual native context. Reducing a
  -- reflected subterm below a syntactic binder in the original context would
  -- misinterpret its de Bruijn variables. Global aliases without local names
  -- are kept intact, preserving their stored cohesion annotations.
  --
  -- A type that mentions a source-local name is normalised. This unfolds
  -- transparent definitions of the file and the copies that a module
  -- application makes of them (a copy is a function with the one clause
  -- copy = original arguments), so that generated axioms appear under
  -- their own names with their actual arguments. The two discreteness
  -- proofs of captured contexts are kept folded: they occur as arguments of
  -- the shape accessors, and their unfolding is a large term with a pattern
  -- lambda.
  --
  -- Reflected syntax omits the parameters of constructors, projections and
  -- projection-like functions and writes `unknown` for them. The result of
  -- `sanitize` never contains `unknown`:
  --   1. names are audited on the syntax as quoted (`clean`, lenient);
  --   2. if no parameter was dropped, that syntax is already complete;
  --   3. otherwise CaptureExplicit.explicit writes the parameters out, and
  --      the explicit term is audited strictly.
  -- Agda's own parameter reconstruction is not used: see CaptureExplicit.
  --
  -- Step S3b: `sanitizeAs typeOf` is the pass; `typeOf` says how the type
  -- that CaptureExplicit.explicit needs is obtained, and is called only
  -- when a parameter was dropped. `sanitize` is the pass with inferType,
  -- as it always was: for a type, inferType gives its sort. A whole TERM
  -- that is a λ has no inferable type; its caller supplies the type.
  sanitizeAs : (Term → TC Term) → LocalPolicy → List Char → Term → TC Term
  sanitizeAs typeOf policy prefix t = expose (hasLocal prefix t) >>= clean 1024 true policy prefix >>= complete
    where
    expose : Bool → TC Term
    expose false = ret t
    expose true = withReduceDefs
      (false , quote telescope-discrete ∷ quote unit-at-discrete ∷ [])
      (normalise t)

    complete : Term → TC Term
    complete u with hasUnknown u
    ... | false = ret u
    ... | true = typeOf u >>= λ sort →
                 explicit sort u >>= clean 1024 false policy prefix

  sanitize : LocalPolicy → List Char → Term → TC Term
  sanitize = sanitizeAs inferType

  sourceOf : Term → TC Term
  sourceOf (def (quote CapturedShape) (arg _ a ∷ arg _ l ∷ arg _ A ∷ [])) = ret A
  sourceOf t = typeError
    (strErr "Use shape at an explicitly declared native type CapturedShape A." ∷ termErr t ∷ [])

  sortLevel : Term → TC Nat
  sortLevel (agda-sort (lit n)) = ret n
  sortLevel t = typeError
    (strErr "Automatic shape capture currently requires fixed finite universe levels; an entire universe-polymorphic telescope has no single finite universe bound." ∷ termErr t ∷ [])

  typeLevel : Term → TC Nat
  typeLevel A = inferType A >>= normalise >>= sortLevel

  -- Infer domains in the original native context, where modalities remain
  -- intact. Strengthen each one into its own preceding telescope prefix.
  collect : LocalPolicy → List Char → Nat → Telescope → TC (Σ Nat (λ _ → Telescope))
  collect policy prefix index [] = ret (zero , [])
  collect policy prefix index ((nm , info) ∷ rest) =
    inferType (var index []) >>= sanitize policy prefix >>= λ full →
    typeLevel full >>= λ l →
    dropNewest (suc index) full >>= λ domain →
    collect policy prefix (suc index) rest >>= λ where
      (largest , domains) → ret (maximum l largest , (nm , v domain) ∷ domains)

  context : Nat → Telescope → Term
  context l [] = def (quote CrispUnitAt) (v (level l) ∷ [])
  context l ((nm , arg _ A) ∷ rest) =
    def (quote CrispΣ)
      (v A ∷ v (lam visible (abs nm (context l rest))) ∷ [])

  applyOne : Term → Term → Term
  applyOne (def n args) x = def n (append args (v x ∷ []))
  applyOne (con n args) x = con n (append args (v x ∷ []))
  applyOne (var i args) x = var i (append args (v x ∷ []))
  applyOne _ _ = unknown -- family below always has a named eliminator head

  family : Nat → Telescope → Term → Term
  family l [] A = def (quote unpack-unit-at)
    (v (def (quote Raise) (v (level l) ∷ v A ∷ [])) ∷ [])
  family l ((nm , _) ∷ rest) A =
    def (quote unpack)
      (v (lam visible (abs nm (lam visible (abs "captured-tail"
        (applyOne (shift 1 0 (family l rest A)) (var 0 [])))))) ∷ [])

  point : Nat → Term
  point zero = con (quote end-at) []
  point (suc n) = con (quote pair) (v (var n []) ∷ v (point n) ∷ [])

  disc : Telescope → Term
  disc [] = def (quote unit-at-discrete) []
  disc (_ ∷ _) = def (quote telescope-discrete) []

  -- An identical payload already registered as an instance is reused;
  -- otherwise ONE axiom is declared, under its record, with the unit
  -- argument after the context; the witness is the axiom applied to tt.
  --
  -- generator checkpoint after fable-impl-11: `offered` is a finite list of
  -- terms that the caller offers to the matcher before the visible
  -- instances (CaptureReuse). It is empty for the macros of this module.
  reuseOrDeclare : List Term → Term → Term → String → TC Term
  reuseOrDeclare offered wrapperType payload reserved = findShapeOffering offered wrapperType payload >>= λ where
    (just witness) → ret witness
    nothing → freshName reserved >>= λ nm →
              -- The payload is closed (requireClosed), so it stands under
              -- the unit binder unchanged.
              declarePostulate (v nm)
                (pi (v (def (quote ⊤) [])) (abs "_" payload)) >>= λ _ →
              ret (def nm (v (con (quote tt) []) ∷ []))

  -- The result is the pair of the wrapper type  CapturedShape {a} {ℓ} A,
  -- written out in full, and the wrapper value. Nothing is unified here.
  -- `total` is the length of the context of the macro call.
  --
  -- Step S3b: the part before the lookup is `payloadAt`. It looks nothing
  -- up and declares nothing; `finish` is that part followed by the commit.
  record Payload : Set where
    constructor payload-of
    field
      wrapperType discreteness stored audited : Term

  payloadAt : LocalPolicy → List Char → Term → Nat → Telescope → Nat → Term → TC Payload
  payloadAt policy prefix A a tel l ctxt =
    let fam = family l tel A
        dc = disc tel
        payload = def (quote RelativeShapeOver) (v ctxt ∷ v dc ∷ v fam ∷ [])
        sort = agda-sort (lit (suc l))
        wrapperType = def (quote CapturedShape) (h (level a) ∷ h (level l) ∷ v A ∷ [])
    in
    requireClosed ctxt >>= λ _ → requireClosed fam >>= λ _ →
    -- Elaborate the payload, then write out every parameter that quotation
    -- dropped from the elaborated term. The explicit term is audited, and
    -- that very term is declared.
    noConstraints (checkType payload sort) >>= explicit sort >>= λ elaborated →
    -- This syntactic audit is essential: inContext [] does NOT remove the
    -- original invocation/module context in Agda's reflection implementation.
    clean 1024 false policy prefix elaborated >>= λ audited →
    requireClosed audited >>= λ _ →
    ret (payload-of wrapperType dc fam audited)

  finish : List Term → LocalPolicy → List Char → Term → Nat → Telescope → Nat → Term → Nat
         → TC (Σ Term (λ _ → Term))
  finish offered policy prefix A a tel l ctxt total =
    payloadAt policy prefix A a tel l ctxt >>= λ where
      (payload-of wrapperType dc fam audited) →
        reuseOrDeclare offered wrapperType audited
          (generatedName (kindOf prefix audited) total) >>= λ witness →
        let value = con (quote captured)
              (v ctxt ∷ v dc ∷ v fam ∷ v witness ∷ v (point (length tel))
              ∷ v (con (quote raise) []) ∷ v (def (quote lower) [])
              ∷ v (def (quote lower-raise) (h unknown ∷ h (level l) ∷ []))
              ∷ v (def (quote raise-lower) []) ∷ [])
        in ret (wrapperType , value)

  -- The capture packs the context it runs in, and the axiom is abstracted
  -- over the context of the macro call. They are the same context unless a
  -- caller has extended it.
  sameContext : Nat → Nat → TC ⊤
  sameContext here native with here == native
  ... | true = ret tt
  ... | false = fail "Automatic shape capture must run in the context of the macro call itself, not under extendContext."

  casePrefix : Telescope → Name → List Char
  casePrefix [] _ = []
  casePrefix (_ ∷ _) n = rootPrefix (primStringToList (primShowQName n))

  -- Step S3b: the capture in its pieces. `captureBody` runs them in the
  -- order in which it always ran their primitives.
  record Site : Set where
    constructor site-of
    field
      original : Telescope
      total : Nat
      prefix : List Char

  -- The context of the call, checked; its native arity; the local prefix.
  siteOf : TC Site
  siteOf =
    checkCrispContext >>= λ _ →
    getContext >>= λ original →
    -- The declaration below is abstracted over the context of the macro call
    -- itself; its length is the native arity recorded in the name.
    inContext [] getContext >>= λ native →
    sameContext (length original) (length native) >>= λ _ →
    -- Only the module of this name is used: it tells which names are local.
    freshName "capture-site" >>= λ name →
    ret (site-of original (length native) (casePrefix original name))

  -- The source of a hole of type CapturedShape A, audited, and its level.
  sourceAt : LocalPolicy → List Char → Term → TC (Σ Term (λ _ → Nat))
  sourceAt policy prefix hole =
    inferType hole >>= reduce >>= sourceOf >>= sanitize policy prefix >>= λ A →
    typeLevel A >>= λ a → ret (A , a)

  -- The largest level of the domains and the telescope, OLDEST FIRST, each
  -- domain audited and strengthened into the entries before it.
  telescopeAt : LocalPolicy → List Char → Telescope → TC (Σ Nat (λ _ → Telescope))
  telescopeAt policy prefix original =
    collect policy prefix zero original >>= λ where
      (largest , backwards) → ret (largest , reverseOnto backwards [])

  captureBody : List Term → LocalPolicy → Term → TC (Σ Term (λ _ → Term))
  captureBody offered policy hole =
    siteOf >>= λ where
      (site-of original total prefix) →
        sourceAt policy prefix hole >>= λ where
          (A , a) →
            telescopeAt policy prefix original >>= λ where
              (largest , tel) →
                let l = maximum a largest
                in finish offered policy prefix A a tel l (context l tel) total

-- Capture without unifying: the explicit wrapper type and the wrapper value.
-- DeclareCapturedShape declares exactly these. Runs under `guarded`: the
-- caller's reconstruction and normalisation flags do not reach it. It
-- checks its own preconditions (crisp context, context of the macro call),
-- so it may be called from a wrapper.
captureCore : LocalPolicy → Term → TC (Σ Term (λ _ → Term))
captureCore policy hole = guarded (captureBody [] policy hole)

-- The same capture, with a finite list of terms offered to the matcher
-- before the visible instances. For a generator that makes several
-- captures in one call and has completed the earlier ones under names of
-- its own: such names are not instances that a search can find. An
-- offered term is used only if it has the audited wrapper type and the
-- audited whole payload; otherwise the capture proceeds as captureCore.
captureCoreOffering : List Term → LocalPolicy → Term → TC (Σ Term (λ _ → Term))
captureCoreOffering offered policy hole = guarded (captureBody offered policy hole)

------------------------------------------------------------------------
-- Step S3b: preparation without declaration.
--
-- A FRAME is what one invocation knows about its context: the prefix that
-- tells which names are local, the audited telescope (oldest first, each
-- domain strengthened into its own prefix), the largest level of a domain,
-- and the native arity. `frame` makes one with the checks of a capture:
-- every variable crisp, relevant and unerased; the current context is the
-- context of the call; every domain passes the audit of a source type.
-- The constructor is private. A Frame is not an authorisation: every
-- program below checks again that it runs in a context of the frame's
-- LENGTH that is the context of the call, and a capture made later in the
-- same call goes through `captureCore` with all its own checks. That
-- check is of the arity, not of the identity of the telescope. A frame
-- is meant to be made and used within one call, in which the context of
-- the call does not change; the direct generator does so.
--
-- The policy is the default one (explicit-only) throughout.
--
--   frameNames fr                 names of the variables, oldest first
--   packedContext fr l            the packed context terminated at level l,
--   packedDiscrete fr             its discreteness witness and the packed
--   packedPoint fr                current point: the terms a capture in
--                                 this context writes
--   prepareType fr t              a TYPE of the context, as `sanitize`
--   prepareTerm fr type t         a TERM of the context of the given type,
--                                 by the same pass; `type` is used only to
--                                 recover dropped parameters
--   prepareSource fr hole         for a hole of type CapturedShape A: the
--                                 source level, the payload level (the
--                                 larger of the source level and the
--                                 largest level of a domain) and the
--                                 family that a capture of A in this
--                                 context stores, after the whole audit of
--                                 its payload. No lookup, no declaration.
--   auditPacked fr type t         for a closed type and a term built by the
--                                 caller: check at the type, write out
--                                 dropped parameters, audit names strictly,
--                                 require closure, check the result at the
--                                 type; the audited term is returned. This
--                                 is the last sequence of a capture before
--                                 its lookup, on an arbitrary term. The
--                                 term must have a named head (its type is
--                                 inferred while parameters are recovered).
-- None of these returns anything that mentions a shape: no K, no ShapeData,
-- no universal property.

private
  data FrameData : Set where
    frame-data : (prefix : List Char) (tel : Telescope) (largest total : Nat)
               → FrameData

  names : Telescope → List String
  names [] = []
  names ((nm , _) ∷ rest) = nm ∷ names rest

  -- The frame's context is the current one and the one of the call.
  inFrame : Nat → TC ⊤
  inFrame total =
    getContext >>= λ here →
    inContext [] getContext >>= λ native →
    sameContext (length here) (length native) >>= λ _ →
    sameContext (length here) total

Frame : Set
Frame = FrameData

frame : TC Frame
frame = guarded (siteOf >>= λ where
  (site-of original total prefix) →
    telescopeAt explicit-only prefix original >>= λ where
      (largest , tel) → ret (frame-data prefix tel largest total))

frameNames : Frame → List String
frameNames (frame-data _ tel _ _) = names tel

packedContext : Frame → Nat → Term
packedContext (frame-data _ tel _ _) l = context l tel

packedDiscrete : Frame → Term
packedDiscrete (frame-data _ tel _ _) = disc tel

packedPoint : Frame → Term
packedPoint (frame-data _ tel _ _) = point (length tel)

prepareType : Frame → Term → TC Term
prepareType (frame-data prefix _ _ total) t = guarded (
  inFrame total >>= λ _ → sanitize explicit-only prefix t)

prepareTerm : Frame → Term → Term → TC Term
prepareTerm (frame-data prefix _ _ total) type t = guarded (
  inFrame total >>= λ _ →
  sanitizeAs (λ _ → ret type) explicit-only prefix t)

prepareSource : Frame → Term → TC (Σ Nat (λ _ → Σ Nat (λ _ → Term)))
prepareSource (frame-data prefix tel largest total) hole = guarded (
  inFrame total >>= λ _ →
  sourceAt explicit-only prefix hole >>= λ where
    (A , a) →
      let l = maximum a largest in
      payloadAt explicit-only prefix A a tel l (context l tel) >>= λ where
        (payload-of _ _ fam _) → ret (a , l , fam))

auditPacked : Frame → Term → Term → TC Term
auditPacked (frame-data prefix _ _ total) type t = guarded (
  inFrame total >>= λ _ →
  requireClosed type >>= λ _ →
  -- 1. The term as built, at the expected type.
  noConstraints (checkType t type) >>=
  -- 2. Dropped parameters, recovered by INFERENCE: the type argument of
  --    `explicit` is left unknown. With an expected type, Agda can solve a
  --    subterm whose check it has postponed (a probe of CaptureExplicit is
  --    one) from that TYPE, where the same constructor stands without its
  --    probe; the parameters would then be dropped again in every round.
  --    Without one, nothing outside the term can be put in its place.
  explicit unknown >>= λ elaborated →
  -- 3. Names, strictly; closure.
  clean 1024 false explicit-only prefix elaborated >>= λ audited →
  requireClosed audited >>= λ _ →
  -- 4. The exact term that is returned, at the expected type again: step 2
  --    did not check against it. The result of this check is discarded.
  noConstraints (checkType audited type) >>= λ _ →
  ret audited)

private
  -- The final unification checks the wrapper against the ORIGINAL native
  -- type of the hole.
  captureWith : LocalPolicy → Term → TC ⊤
  captureWith policy hole = guarded (captureCore policy hole >>= λ where
    (_ , value) → unify hole value)

-- The function behind the macro `shape`, for callers that wrap it.
capture : Term → TC ⊤
capture = captureWith explicit-only

macro
  -- The source may mention an earlier shape of the same file when all of
  -- that shape's parameters are explicit (function style, sibling module).
  shape : Term → TC ⊤
  shape = capture

  -- Also accepts an earlier shape of the SAME module, reached through the
  -- module's own parameters. NOT part of the default interface: read
  -- FABLE-REVIEW-01.txt, C03, and FABLE-REVIEW-03.txt, section 2.5, before
  -- relying on it.
  shape-in-module : Term → TC ⊤
  shape-in-module = captureWith ambient-too
