{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The READER of the staged route: in the EMPTY context, recover the closed
-- metadata of a diagram that was declared inside a context, from the NAME
-- of its descriptor. Claude (Fable), 13 November 2026; after fable-impl-14
-- (HANDOFF-31; S3-METADATA-STAGING-PREFLIGHT-01 section 3;
-- S3-METADATA-NATIVE-FIDELITY-01). The account for a user is
-- STAGE-CAPTURED-DIAGRAM.txt.
--
--   module Local (@♭ b : Bool) (@♭ v : Code b) where
--     unquoteDecl cells descriptor = declareStagedDiagram cells descriptor …
--
--   unquoteDecl index = readCapturedDiagram index (quote Local.descriptor)
--
-- declares ONE definition
--   index : DiagramMeta ℓ
-- and nothing else. It declares no axiom and requests no shape. It does
-- not apply the descriptor to anything and uses no point of the context:
-- a telescope that begins in an empty type is read in the same way.
--
-- WHAT IT DOES, in order.
--   1. Both the context of the call and the current context must be
--      empty; otherwise nothing is read. (Inside a module with parameters
--      getType instantiates the shared ones, and a declaration is
--      abstracted over them.)
--   2. getType of the name, without normalisation or reconstruction. The
--      type must be a telescope of VISIBLE, relevant, unerased binders
--      followed by  CapturedDiagramFor {ℓ} m  with ℓ a level numeral.
--      Hidden and instance binders are refused, not rewritten.
--   3. m must be closed AS WRITTEN: no variable of the telescope occurs
--      in it. A definition of the module is a function of those
--      variables, so an index that goes through one is refused too, even
--      when its value does not depend on them. Nothing is unfolded and no
--      argument is erased to make an index pass.
--   4. AUDIT, by the audit of the capture frontend and not by a second
--      one: CaptureShape.frame, which here is the frame of the empty
--      context, and CaptureShape.auditPacked at the type DiagramMeta ℓ.
--      That is: the term as read is checked at the type; the parameters
--      that reflected syntax dropped are written out by CaptureExplicit;
--      unknowns, metas and pattern lambdas are refused; closure is
--      required; and the explicit term is checked at the type again. The
--      explicit term m′ is the candidate. In the empty context no name is
--      local to the call, so the audit of names has nothing to refuse:
--      what makes m′ closed is that it has no free variable and that it
--      is checked where there is no context.
--      This shows that m′ is a well-typed closed metadata term. It does
--      NOT show that m′ is the index of the descriptor: reflected syntax
--      has no cohesion annotations and drops parameters, and what was
--      re-elaborated may be a different term (StagedReaderCrispInside).
--   5. THE CHECK. The candidate type
--        CrispPi {a1} {b1} A1 (λ x1 → … CrispPi {an} {bn} An (λ xn →
--          CapturedDiagramFor {ℓ} m′))
--      is formed with the domains as read and the native former CrispPi:
--      the reflected λ gets its crisp binder from the native type of
--      CrispPi's second argument. Its levels are taken from an
--      elaboration of the candidate alone, before the name is looked at,
--      and then written out as numerals; nothing else of that
--      elaboration is used. So the candidate has FIXED LEVELS and the
--      EXPLICIT AUDITED index m′. Its domains are the quoted domains as
--      read. The candidate is required to have no free variable, no
--      meta and no unknown; that does not say that every implicit
--      argument inside a domain is written out. (fable-impl-16: this
--      sentence replaces "complete syntax with nothing left to infer",
--      which claimed more; M15-SOURCE-REVIEW-01.) What Agda fills in
--      there is not trusted: the next step decides.
--      Then Agda checks
--        the ORIGINAL NAME, unapplied, at the candidate type.
--      The name has its native type, with its real binders. So this
--      compares the real telescope with the candidate's, binder by
--      binder with their cohesion, and then, under the formal variables,
--      CapturedDiagramFor m with CapturedDiagramFor m′: the head is
--      rigid and the index relevant, so m is compared with m′ by
--      conversion. It is not a comparison of two quotations. The check is
--      speculative: its elaborated result is discarded.
--   6. Only now is the index declared, with body m′.
--
-- WHAT IS AND IS NOT CLAIMED. For a successful call: m′ is closed, has
-- type DiagramMeta ℓ in the empty context, and the descriptor, at every
-- value of its parameters, has the type CapturedDiagramFor m′ by
-- conversion of the indices. The check is by conversion, so it is
-- stricter than equivalence of diagrams, and a failure is a refusal of
-- this reader, not a statement that no index exists. The reader does not
-- check the descriptor's PRODUCER: that the descriptor describes what the
-- user wrote is the business of declareStagedDiagram and its two native
-- checks. Nothing here is a hidden-dependency audit of the telescope's
-- own domains: they are taken as read, required to have no free
-- variable, meta or unknown, and compared with the native telescope of
-- the name by the check.
-- No shape, product law or Nullstellensatz is declared, looked up or
-- transported here; an index is a candidate for staging, and what is
-- staged for it is declared by the existing entry points.
module ReadCapturedDiagram where

open import Foundations
open import CaptureSyntax using (requireClosed)
open import CaptureExplicit using (guarded)
open import CaptureShape using (frame; auditPacked)
open import DiagramMetadata using (CrispPi; DiagramMeta; CapturedDiagramFor)
open import Agda.Builtin.Reflection
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _<_; _-_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using (String)

private
  infixl 1 _>>=_
  _>>=_ = bindTC
  ret = returnTC

  -- Progress, with  -v capture.staging:5.
  stage : String → TC ⊤
  stage s = debugPrint "capture.staging" 5 (strErr s ∷ [])

  v : {A : Set} → A → Arg A
  v = arg (arg-info visible (modality relevant quantity-ω))

  h : {A : Set} → A → Arg A
  h = arg (arg-info hidden (modality relevant quantity-ω))

  length : {A : Set} → List A → Nat
  length [] = zero
  length (_ ∷ xs) = suc (length xs)

  levelAt : Nat → Term
  levelAt zero = def (quote lzero) []
  levelAt (suc n) = def (quote lsuc) (v (levelAt n) ∷ [])

  -- A closed level numeral.
  numeral : Term → Maybe Nat
  numeral (def (quote lzero) []) = just zero
  numeral (def (quote lsuc) (arg _ t ∷ [])) with numeral t
  ... | just n = just (suc n)
  ... | nothing = nothing
  numeral _ = nothing

  ----------------------------------------------------------------------
  -- Refusals.

  open-context : {A : Set} → TC A
  open-context = typeError
    (strErr "readCapturedDiagram reads a completed descriptor from OUTSIDE the context it was declared in, and runs only in the empty context: outside every module with parameters and every definition with arguments. Inside a context the type of the descriptor would be instantiated at shared parameters and the index would be declared as a function of the context. Nothing was read; nothing is declared." ∷ [])

  -- A check only: it declares nothing.
  both-empty : Telescope → Telescope → TC ⊤
  both-empty [] [] = ret tt
  both-empty _ _ = open-context

  not-descriptor : {A : Set} → Name → Term → TC A
  not-descriptor n t = typeError
    ( strErr "readCapturedDiagram: " ∷ nameErr n
    ∷ strErr " is not a descriptor. Its type must be a telescope of visible binders ending in  CapturedDiagramFor m ; declareStagedDiagram declares such a name next to the bundle. The type ends in: "
    ∷ termErr t ∷ [])

  unsupported-binder : {A : Set} → Name → String → TC A
  unsupported-binder n nm = typeError
    ( strErr "readCapturedDiagram: the binder " ∷ strErr nm
    ∷ strErr " in the type of " ∷ nameErr n
    ∷ strErr " is hidden, an instance argument, irrelevant or erased. Only a telescope of visible module parameters is read; another binder is refused rather than rewritten as a visible one." ∷ [])

  symbolic-level : {A : Set} → Name → Term → TC A
  symbolic-level n l = typeError
    ( strErr "readCapturedDiagram: the level of the descriptor " ∷ nameErr n
    ∷ strErr " is not a fixed numeral: " ∷ termErr l ∷ [])

  retained : {A : Set} → Name → String → TC A
  retained n nm = typeError
    ( strErr "readCapturedDiagram: the metadata index in the type of " ∷ nameErr n
    ∷ strErr " mentions the variable " ∷ strErr nm
    ∷ strErr " of its telescope, directly or through a definition of the module (such a definition is a function of the variables of the module, also when its value does not depend on them). The index of a descriptor must be closed as written. Nothing is unfolded and no argument is erased to make it so; nothing is declared." ∷ [])

  incomplete-domain : {A : Set} → Name → TC A
  incomplete-domain n = typeError
    ( strErr "readCapturedDiagram: the telescope in the type of " ∷ nameErr n
    ∷ strErr " cannot be written out completely from reflected syntax (a domain has a dropped parameter, or a level of the telescope is not a fixed numeral). The candidate type would have to be completed by inference, so the descriptor is refused." ∷ [])

  ----------------------------------------------------------------------
  -- The type of a descriptor, taken apart.

  -- A variable of the telescope that the term mentions: its de Bruijn
  -- index counted from the newest binder of the telescope. `depth` is the
  -- number of binders of the term itself that are in scope. The calling
  -- context is empty, so every other variable is one of the telescope.
  -- `unknown` stands for a dropped parameter and is left to the audit;
  -- metas and pattern lambdas are refused there.
  mutual
    mention : Nat → Term → Maybe Nat
    mention depth (var i args) with i < depth
    ... | true = mentionArgs depth args
    ... | false = just (i - depth)
    mention depth (con _ args) = mentionArgs depth args
    mention depth (def _ args) = mentionArgs depth args
    mention depth (lam _ (abs _ t)) = mention (suc depth) t
    mention depth (pi (arg _ a) (abs _ b)) with mention depth a
    ... | just i = just i
    ... | nothing = mention (suc depth) b
    mention depth (agda-sort (set t)) = mention depth t
    mention depth (agda-sort (prop t)) = mention depth t
    mention depth (agda-sort _) = nothing
    mention depth (lit _) = nothing
    mention depth (meta _ args) = mentionArgs depth args
    mention depth (pat-lam _ args) = mentionArgs depth args
    mention depth unknown = nothing

    mentionArgs : Nat → List (Arg Term) → Maybe Nat
    mentionArgs depth [] = nothing
    mentionArgs depth (arg _ t ∷ ts) with mention depth t
    ... | just i = just i
    ... | nothing = mentionArgs depth ts

  Binder : Set
  Binder = Σ String (λ _ → Term)

  -- OLDEST FIRST; each domain in the scope of the binders before it.
  record Telescoped : Set where
    constructor telescoped
    field
      binders : List Binder
      level index : Term

  peel : Name → Term → TC Telescoped
  peel n (pi (arg (arg-info visible (modality relevant quantity-ω)) domain)
             (abs nm body)) =
    peel n body >>= λ where
      (telescoped binders l m) → ret (telescoped ((nm , domain) ∷ binders) l m)
  peel n (pi _ (abs nm _)) = unsupported-binder n nm
  peel n (def (quote CapturedDiagramFor) (arg _ l ∷ arg _ m ∷ [])) =
    ret (telescoped [] l m)
  peel n t = not-descriptor n t

  -- The name of the binder with the given index from the NEWEST.
  nameFromNewest : List Binder → Nat → String
  nameFromNewest binders i = pick (length binders - suc i) binders
    where
    pick : Nat → List Binder → String
    pick _ [] = "?"
    pick zero ((nm , _) ∷ _) = nm
    pick (suc k) (_ ∷ rest) = pick k rest

  closed-as-written : Name → List Binder → Term → TC ⊤
  closed-as-written n binders m with mention zero m
  ... | nothing = ret tt
  ... | just i = retained n (nameFromNewest binders i)

  ----------------------------------------------------------------------
  -- The candidate type.

  -- With the two levels of every CrispPi left to Agda.
  inferred : List Binder → Term → Term
  inferred [] final = final
  inferred ((nm , domain) ∷ rest) final =
    def (quote CrispPi)
      (v domain ∷ v (lam visible (abs nm (inferred rest final))) ∷ [])

  Levels : Set
  Levels = List (Σ Nat (λ _ → Nat))

  -- The levels that Agda found for the candidate, read off its
  -- elaboration; nothing else of that elaboration is used.
  levelsOf : Nat → Term → Maybe Levels
  levelsOf zero _ = just []
  levelsOf (suc k)
    (def (quote CrispPi)
      (arg _ a ∷ arg _ b ∷ arg _ _ ∷ arg _ (lam _ (abs _ body)) ∷ []))
    with numeral a | numeral b | levelsOf k body
  ... | just a′ | just b′ | just rest = just ((a′ , b′) ∷ rest)
  ... | _ | _ | _ = nothing
  levelsOf (suc k) _ = nothing

  -- With every level written out.
  written : List Binder → Levels → Term → Term
  written ((nm , domain) ∷ rest) ((a , b) ∷ ls) final =
    def (quote CrispPi)
      (h (levelAt a) ∷ h (levelAt b)
       ∷ v domain ∷ v (lam visible (abs nm (written rest ls final))) ∷ [])
  written _ _ final = final

readCapturedDiagram : Name → Name → TC ⊤
readCapturedDiagram index descriptor = guarded (
  -- 1. The empty context.
  inContext [] getContext >>= λ calling →
  getContext >>= λ current →
  both-empty calling current >>= λ _ →
  -- 2. The type of the descriptor.
  stage "the type of the descriptor" >>= λ _ →
  getType descriptor >>= peel descriptor >>= λ where
    (telescoped binders levelTerm m) → level descriptor levelTerm >>= λ l →
      -- 3. Closed as written.
      closed-as-written descriptor binders m >>= λ _ →
      -- 4. The audit of the capture frontend, at the frame of the empty
      --    context.
      stage "the audit of the index" >>= λ _ →
      frame >>= λ fr →
      let type = def (quote DiagramMeta) (v (levelAt l) ∷ []) in
      auditPacked fr type m >>= λ audited →
      -- 5. The candidate type, its levels from the candidate alone, and
      --    the original name at that type.
      stage "the candidate type" >>= λ _ →
      let final = def (quote CapturedDiagramFor)
                    (h (levelAt l) ∷ v audited ∷ [])
      in
      catchTC
        (noConstraints (checkType (inferred binders final) unknown))
        (incomplete-domain descriptor) >>= λ elaborated →
      levels descriptor (levelsOf (length binders) elaborated) >>= λ ls →
      let candidate = written binders ls final in
      catchTC (requireClosed candidate) (incomplete-domain descriptor) >>= λ _ →
      stage "the original name at the candidate type" >>= λ _ →
      runSpeculative
        (noConstraints (checkType (def descriptor []) candidate) >>= λ _ →
         ret (tt , false)) >>= λ _ →
      -- 6. The index.
      stage "the index" >>= λ _ →
      declareDef (v index) type >>= λ _ →
      defineFun index (clause [] [] audited ∷ []))
  where
  level : Name → Term → TC Nat
  level n t with numeral t
  ... | just l = ret l
  ... | nothing = symbolic-level n t

  levels : Name → Maybe Levels → TC Levels
  levels n (just ls) = ret ls
  levels n nothing = incomplete-domain n
