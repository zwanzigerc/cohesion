{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The DIRECT generator: a diagram stated natively INSIDE a crisp context,
-- one public name, at most two new shape axioms. Claude (Fable),
-- 13 November 2026; steps S3b and S3c of the direct in-module route, after
-- fable-impl-13 (HANDOFF-29, HANDOFF-30; DIRECT-OPEN-DIAGRAM-ROUTE-01;
-- S3-PACKED-DATA-AUDIT-SEAM-01; FABLE-REVIEW-06 section 4). The account
-- for a user is DECLARE-CAPTURED-DIAGRAM.txt.
--
-- Use, in a module whose parameters are all crisp:
--
--   module Local (@♭ b : Bool) (@♭ v : Code b) where
--     unquoteDecl cells =
--       declareCapturedDiagram cells (bool-dec ∷ code-dec b ∷ [])
--         dB B-set dC C-set f A
--
-- where f : C → B, A : B → Set ℓ and the four evidence terms are the
-- user's native typed terms in that context, written inline or as names
-- of definitions, and the list has one decision procedure for the type of
-- each context variable, oldest first. The result is
--   cells : CapturedDiagram ℓ
-- for DiagramBundle.AssembleCaptured. The user writes no packed context,
-- no packed map or family, no point, no At and no shape data.
--
-- A second entry point, declareStagedDiagram (at the end of this file,
-- step 9; fable-impl-15), declares in the same call a second name, the
-- DESCRIPTOR of the bundle: the bundle at a type that has the audited
-- closed data of the diagram as its index. declareCapturedDiagram itself
-- does what it did in fable-impl-14: its steps 1 to 8 are the private
-- program `generate`, which both entry points run, with the same
-- primitives in the same order as before; the record of audited terms
-- that it returns has the two presentation families in addition.
--
-- WHAT IT DOES, in order. Steps 1 to 5 look nothing up and declare nothing.
--   1. FRAME (CaptureShape.frame). The context must be the context of the
--      call, non-empty, every variable crisp, relevant and unerased; every
--      domain is audited as a capture audits it.
--   2. SOURCES (CaptureShape.prepareSource). The two local total sources
--      Σ B A and Σ C (A ∘ f), in the native spelling formed from the typed
--      arguments, are prepared as a capture prepares them, up to and
--      including the audit of their payload types. This gives the two
--      families that the captures will STORE. One common level: a context
--      with a type above the level of the diagram is refused.
--   3. LEAVES. Each of B, C, dB, B-set, dC, C-set, f, A is quoted from its
--      native argument and passed through the same pass as a source type
--      (CaptureShape.prepareType, prepareTerm): source-local names are
--      exposed in the native context, dropped parameters are written out,
--      names are audited. The map is prepared on its own, whatever the
--      family is: it is never read off a source type. Each decision
--      procedure is quoted from its native typed entry and prepared as a
--      TERM in the full context, with its type; then both are
--      strengthened past the entry's own variable and all newer ones. A
--      procedure that mentions them is refused, by name of the variable.
--   4. PACKING. Every packed datum is ONE INLINE CLOSED TERM: the nest of
--      the combinators unpack-dependent (or unpack-crisp, for a datum at a
--      crisp point), unpack-crisp, …, unpack-end-crisp on a motive and the
--      prepared leaf, its variables rebound by the combinators. No helper
--      is declared in the module; the terms mention global names of the
--      library only (the combinators; paired, which is the constructor
--      pair as a function; OverTotal, LocalTotal, Reindexed; Presentation,
--      lowering and the four accessors of Presented).
--      For each stored family ONE presentation family is packed,
--        (g : G) → Presentation (F g) (LocalTotal … g),
--      with the leaf `lowering`: the capture's own source maps and laws.
--      It is typed only if at EVERY packed point the family of step 2 is
--      the raised copy of the packed local total source. The four fields
--      of the bundle are its four components.
--      Each term built here is checked against its closed type and
--      audited as a payload is (CaptureShape.auditPacked): parameters
--      written out, names audited strictly, closure required, and the
--      audited term checked at the type. The audited terms are what is
--      declared; the components of a presentation are an accessor of the
--      library applied to audited terms, every argument written out.
--   5. FIRST NATIVE CHECK. Agda checks the direct constructor
--        packed G dG dec B̃ C̃ dB̃ B̃-set dC̃ C̃-set f̃ Ã g₀ FB FC <presentations>
--      at the type  PackedDiagramOf dB B-set dC C-set f A  formed from the
--      user's ORIGINAL typed arguments (DiagramBundle). Its arguments are
--      all the fields of the bundle except the two payloads, at the types
--      of the bundle. So every closed field is checked natively at its
--      type, and the packed data at the current point convert to what the
--      user wrote: the map and each evidence term separately.
--   6. THE TWO CAPTURES, through the unchanged audited capture
--      (DeclareCapturedShape.declareSeed), each completed as an ordinary
--      definition under a fresh name; the first is offered to the second.
--      Each is a lookup or ONE new axiom. They prepare their sources
--      again, by the same code, with all their own checks.
--   7. THE BUNDLE: the public name is declared as an INSTANCE of
--      CapturedDiagram ℓ and defined as the constructor on the audited
--      terms, the packed current point, and the whole payloads of the two
--      completed captures.
--   8. SECOND NATIVE CHECK. Agda checks the direct constructor
--        bundled <the public name>
--      at  CapturedDiagramOf dB B-set dC C-set f A sB sC <the public name>
--      where sB, sC are the two completed captures at their native types:
--      the fields of the bundle at its stored point are the user's
--      arguments, and the wrappers that the library rebuilds from the
--      bundle ARE the two captures. sB, sC and the bundle come out of the
--      reflection monad as ordinary values and are ordinary indices of
--      that type; no accessor is applied to them.
-- If any step fails, the declaration fails as a whole.
--
-- WHAT IS AND IS NOT CLAIMED. The generator has no axiom-declaring
-- primitive: every shape postulate of a call is emitted by CaptureShape.
-- Its own declarations are definitions. The two payloads are contextual
-- choices at the variables of the context; nothing treats them as closed
-- constants, and no fibre is promoted to terminal shape data.
-- WHAT IS REGISTERED (step S3c). Only the public bundle, as an instance
-- of its own head. The two completed captures are fresh names, not in
-- scope and not candidates of any search. A later request, by `shape`,
-- declareShape or a generator, in the SAME context, finds the bundle and
-- tries its two rebuilt wrappers through the matcher of CaptureReuse;
-- the captures of this generator go through that lookup too, so a prior
-- visible seed or bundle is used. The bundle is declared after both of
-- its captures, so it is never a candidate for them.
-- SCOPE. The telescope is arbitrary in length; the context must be
-- non-empty (at top level the closed form
-- DeclareDiagram.declareClosedDiagram applies). Levels are fixed
-- numerals, one for the whole diagram.
module DeclareCapturedDiagram where

open import Foundations
open import Agda.Primitive using (Setω)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureUnpack
  using (unpack-crisp; unpack-end-crisp; paired;
         unpack-dependent-over; unpack-crisp-over)
open import CaptureSyntax using (shift; dropNewest)
open import CaptureExplicit using (guarded)
open import CaptureShape
  using (Frame; frame; frameNames; packedContext; packedDiscrete;
         packedPoint; prepareType; prepareTerm; prepareSource; auditPacked)
open import DeclareCapturedShape using (declareSeed)
open import DecidableBase using (DecEq; unit-at-dec)
open import DecidableTelescope using (dependent-context-dec)
open import DiagramBundle
open import DiagramMetadata using (CapturedDiagramFor; describe; meta-of)
open import Agda.Builtin.Reflection
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_; _<_; _==_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String; primStringAppend; primShowNat)

-- One decision procedure for the type of each variable of the context,
-- OLDEST FIRST. An entry is written in the context itself and may mention
-- the variables before its own; it is a native typed term, not syntax.
data Deciders : Setω where
  [] : Deciders
  _∷_ : ∀ {a} {X : Set a} → DecEq X → Deciders → Deciders

infixr 5 _∷_

private
  infixl 1 _>>=_
  _>>=_ = bindTC
  ret = returnTC

  -- Progress, with  -v capture.diagram:5.
  stage : String → TC ⊤
  stage s = debugPrint "capture.diagram" 5 (strErr s ∷ [])

  v : {A : Set} → A → Arg A
  v = arg (arg-info visible (modality relevant quantity-ω))

  h : {A : Set} → A → Arg A
  h = arg (arg-info hidden (modality relevant quantity-ω))

  inst : {A : Set} → A → Arg A
  inst = arg (arg-info instance′ (modality relevant quantity-ω))

  fail : {A : Set} → String → TC A
  fail s = typeError (strErr s ∷ [])

  length : {A : Set} → List A → Nat
  length [] = zero
  length (_ ∷ xs) = suc (length xs)

  append : {A : Set} → List A → List A → List A
  append [] ys = ys
  append (x ∷ xs) ys = x ∷ append xs ys

  _and_ : Bool → Bool → Bool
  true and b = b
  false and _ = false

  -- Application of a term with a named head. Every term this is used on
  -- is built below with such a head.
  app : Term → Term → Term
  app (def n args) x = def n (append args (v x ∷ []))
  app (con n args) x = con n (append args (v x ∷ []))
  app (var i args) x = var i (append args (v x ∷ []))
  app _ _ = unknown

  setAt : Nat → Term
  setAt l = agda-sort (lit l)

  levelAt : Nat → Term
  levelAt zero = def (quote lzero) []
  levelAt (suc n) = def (quote lsuc) (v (levelAt n) ∷ [])

  -- A → B for two terms of the same scope.
  arrow : Term → Term → Term
  arrow a b = pi (v a) (abs "_" (shift 1 0 b))

  ----------------------------------------------------------------------
  -- The nest of eliminators over a telescope x1 … xn (n ≥ 1).
  --
  --   unpack-dependent-over A B (λ g → M g) (λ x1 t1 →
  --     unpack-crisp (λ t → M (paired x1 t)) (λ x2 t2 →
  --       …
  --         unpack-end-crisp (λ t → M (paired x1 (… (paired xn t)))) LEAF tn) … t1)
  --
  -- and the same with unpack-crisp-over outermost for a datum at a crisp
  -- point; A and B are the two parameters of the packed context.
  -- Under the binders x1 t1 … xi ti the variable xj has index 2 (i − j) + 1.
  -- A motive is a function of the packed point, given as a term of the
  -- scope in which the motive is placed.

  -- paired x1 (paired x2 (… (paired xi tail))) under x1 t1 … xi ti and
  -- `extra` further binders. `paired` is the constructor pair as a
  -- function (CaptureUnpack): a generated term has no constructor whose
  -- parameters would have to be recovered.
  pointUnder : Nat → Nat → Term → Term
  pointUnder zero extra tail = tail
  pointUnder (suc k) extra tail =
    pointUnder k (extra + 2) (def (quote paired) (v (var (suc extra) []) ∷ v tail ∷ []))

  motiveAt : (Term → Term) → Nat → Term
  motiveAt M i = lam visible (abs "tail" (M (pointUnder i 1 (var 0 []))))

  -- The eliminator of the tail ti, which is variable 0, with the names of
  -- the variables still to be bound.
  rest : (Term → Term) → Nat → List String → Term → Term
  rest M i [] leaf =
    def (quote unpack-end-crisp) (v (motiveAt M i) ∷ v leaf ∷ v (var 0 []) ∷ [])
  rest M i (nm ∷ nms) leaf =
    def (quote unpack-crisp)
      (v (motiveAt M i)
       ∷ v (lam visible (abs nm (lam visible (abs "tail" (rest M (suc i) nms leaf)))))
       ∷ v (var 0 []) ∷ [])

  -- The outermost combinator is given the two parameters of the packed
  -- context, the type of the oldest variable and the family of the rest,
  -- as written by CaptureShape (unpack-dependent-over, unpack-crisp-over).
  -- Then a nest determines its own domains: a leaf need not mention every
  -- variable of the context (a leaf that is a closed type mentions none),
  -- and nothing is left to be inferred from the type the nest is checked
  -- against.
  elimWith : Name → Term → (Term → Term) → List String → Term → Term
  elimWith outer G M (nm ∷ nms) leaf with G
  ... | def _ (arg _ A ∷ arg _ B ∷ []) =
    def outer
      (v A ∷ v B
       ∷ v (motiveAt M zero)
       ∷ v (lam visible (abs nm (lam visible (abs "tail" (rest M 1 nms leaf))))) ∷ [])
  ... | _ = unknown
  elimWith outer G M [] leaf = unknown

  -- A motive over an ordinary packed point; over a crisp one.
  elim elim♭ : Term → (Term → Term) → List String → Term → Term
  elim = elimWith (quote unpack-dependent-over)
  elim♭ = elimWith (quote unpack-crisp-over)

  -- A prepared term of the native context, as a leaf: under the 2n binders
  -- of the nest the context variable with native index k has index 2k + 1.
  mutual
    weave : Nat → Term → Term
    weave d (var i args) with i < d
    ... | true = var i (weaveArgs d args)
    ... | false = var (d + suc (2 * (i - d))) (weaveArgs d args)
    weave d (con c args) = con c (weaveArgs d args)
    weave d (def f args) = def f (weaveArgs d args)
    weave d (lam vis (abs nm b)) = lam vis (abs nm (weave (suc d) b))
    weave d (pi (arg i a) (abs nm b)) = pi (arg i (weave d a)) (abs nm (weave (suc d) b))
    weave d (agda-sort (set l)) = agda-sort (set (weave d l))
    weave d (agda-sort (prop l)) = agda-sort (prop (weave d l))
    weave d t@(agda-sort _) = t
    weave d t@(lit _) = t
    -- Not in a prepared term (CaptureShape's audit refuses them).
    weave d (meta _ _) = unknown
    weave d (pat-lam _ _) = unknown
    weave d unknown = unknown

    weaveArgs : Nat → List (Arg Term) → List (Arg Term)
    weaveArgs d [] = []
    weaveArgs d (arg i t ∷ ts) = arg i (weave d t) ∷ weaveArgs d ts

  leafOf : Term → Term
  leafOf = weave zero

  -- The type of a datum over an ordinary point of the packed context G.
  over : Term → (Term → Term) → Term
  over G M = pi (v G) (abs "g" (M (var 0 [])))

  ----------------------------------------------------------------------
  -- Motives.

  familyMotive : Nat → Term → Term
  familyMotive l _ = setAt l

  mapMotive : (Term → Term) → (Term → Term) → Term → Term
  mapMotive X Y pt = arrow (X pt) (Y pt)

  familyOverMotive : Term → Nat → Term → Term
  familyOverMotive X l pt = arrow (app X pt) (setAt l)

  discreteMotive : Term → Term → Term
  discreteMotive X pt = def (quote Discrete) (v (app X pt) ∷ [])

  setMotive : Term → Term → Term
  setMotive X pt = def (quote IsSet) (v (app X pt) ∷ [])

  -- Presentation (F pt) (T pt)
  presentationMotive : (Term → Term) → (Term → Term) → Term → Term
  presentationMotive F T pt = def (quote Presentation) (v (F pt) ∷ v (T pt) ∷ [])

  ----------------------------------------------------------------------
  -- Decision procedures.

  -- A procedure that uses its own variable or a later one is not a
  -- procedure over the prefix.
  notOverPrefix : {A : Set} → String → TC A
  notOverPrefix nm = typeError
    ( strErr "declareCapturedDiagram: the decision procedure given for the context variable "
    ∷ strErr nm
    ∷ strErr " may mention only the variables BEFORE that variable. Its term or its type mentions the variable itself or a later one (possibly through a definition of the module), so it is not a procedure for every value of the earlier variables. This is a rule of the packing, not a statement that no such procedure exists."
    ∷ [])

  -- A prepared procedure with the prepared type it decides, in the full
  -- context.
  record Hint : Set where
    constructor hint
    field
      domain procedure : Term

  -- Entry i of n is strengthened past the n − i + 1 newest variables:
  -- its own and every newer one. Both the type and the TERM must survive.
  strengthen : Nat → List String → List Hint → TC (List Term)
  strengthen k (nm ∷ nms) (hint X d ∷ hs) =
    catchTC (dropNewest k X >>= λ _ → dropNewest k d) (notOverPrefix nm) >>= λ d′ →
    strengthen (k - 1) nms hs >>= λ ds → ret (d′ ∷ ds)
  strengthen _ _ _ = ret []

  -- dependent-context-dec d1 (λ x1 → dependent-context-dec d2 (λ x2 → … unit-at-dec))
  decider : List String → List Term → Term
  decider (nm ∷ nms) (t ∷ ts) =
    def (quote dependent-context-dec)
      (v t ∷ v (lam visible (abs nm (decider nms ts))) ∷ [])
  decider _ _ = def (quote unit-at-dec) []

  -- Each entry is quoted from its NATIVE typed value, with the type that
  -- Agda gave it at the call, and passed through the pass of a source.
  quoteDeciders : Frame → Deciders → TC (List Hint)
  quoteDeciders fr [] = ret []
  quoteDeciders fr (_∷_ {X = X} d ds) =
    quoteTC X >>= prepareType fr >>= λ X′ →
    quoteTC d >>= prepareTerm fr (def (quote DecEq) (v X′ ∷ [])) >>= λ d′ →
    quoteDeciders fr ds >>= λ rest → ret (hint X′ d′ ∷ rest)

  ----------------------------------------------------------------------
  -- Refusals.

  nonEmpty : List String → TC ⊤
  nonEmpty [] = fail "declareCapturedDiagram states a diagram INSIDE a context and needs at least one crisp variable. At top level, outside every module with parameters, use declareClosedDiagram."
  nonEmpty (_ ∷ _) = ret tt

  countsAgree : Nat → Nat → TC ⊤
  countsAgree variables given with variables == given
  ... | true = ret tt
  ... | false = typeError
    ( strErr "declareCapturedDiagram needs exactly one decision procedure for the type of each variable of the context, oldest first. Variables: "
    ∷ strErr (primShowNat variables) ∷ strErr "; procedures given: "
    ∷ strErr (primShowNat given) ∷ strErr "." ∷ [])

  -- The source level a and the payload level l of the two sources.
  oneLevel : Nat → Nat → Nat → Nat → TC ⊤
  oneLevel aB lB aC lC with ((aB == lB) and (aC == lC)) and (aB == aC)
  ... | true = ret tt
  ... | false = typeError
    ( strErr "declareCapturedDiagram: the context has a type in a universe above the level of the diagram (level "
    ∷ strErr (primShowNat aB) ∷ strErr "; the context needs level "
    ∷ strErr (primShowNat lB)
    ∷ strErr "). The bundle has one level: state the bases and the family at the level of the context." ∷ [])

  ----------------------------------------------------------------------
  -- The audited data of a call.

  record Leaves : Set where
    constructor leaves
    field
      B C dB B-set dC C-set f A : Term

  record Packed : Set where
    constructor packed-data
    field
      G dG dec B C dB B-set dC C-set f A : Term
      FB FC outB inB secB retB outC inC secC retC : Term
      -- The two audited presentation families, of which the eight fields
      -- above are the components.
      presB presC : Term

  module _ {@♭ ℓ : Level} {@♭ B C : Set ℓ} where

    prepareLeaves : Frame → Nat
      → (@♭ dB : Discrete B) (@♭ B-set : IsSet B)
      → (@♭ dC : Discrete C) (@♭ C-set : IsSet C)
      → (@♭ f : C → B) (@♭ A : B → Set ℓ) → TC Leaves
    prepareLeaves fr l dB B-set dC C-set f A =
      quoteTC B >>= prepareType fr >>= λ B′ →
      quoteTC C >>= prepareType fr >>= λ C′ →
      quoteTC dB >>= prepareTerm fr (def (quote Discrete) (v B′ ∷ [])) >>= λ dB′ →
      quoteTC B-set >>= prepareTerm fr (def (quote IsSet) (v B′ ∷ [])) >>= λ B-set′ →
      quoteTC dC >>= prepareTerm fr (def (quote Discrete) (v C′ ∷ [])) >>= λ dC′ →
      quoteTC C-set >>= prepareTerm fr (def (quote IsSet) (v C′ ∷ [])) >>= λ C-set′ →
      -- The map on its own.
      quoteTC f >>= prepareTerm fr (arrow C′ B′) >>= λ f′ →
      quoteTC A >>= prepareTerm fr (arrow B′ (setAt l)) >>= λ A′ →
      ret (leaves B′ C′ dB′ B-set′ dC′ C-set′ f′ A′)

    -- The families that captures of the two local total sources store,
    -- and the common level. The holes exist only inside the speculation.
    prepareSources : Frame → (@♭ f : C → B) (@♭ A : B → Set ℓ)
                   → TC (Σ Nat (λ _ → Σ Term (λ _ → Term)))
    prepareSources fr f A =
      quoteTC (CapturedShape {ℓ = ℓ} (Σ B A)) >>= λ typeB →
      quoteTC (CapturedShape {ℓ = ℓ} (Σ C (A ∘ f))) >>= λ typeC →
      stored typeB >>= λ where
        (aB , lB , FB) → stored typeC >>= λ where
          (aC , lC , FC) →
            oneLevel aB lB aC lC >>= λ _ → ret (aB , FB , FC)
      where
      stored : Term → TC (Σ Nat (λ _ → Σ Nat (λ _ → Term)))
      stored type = runSpeculative (
        checkType unknown type >>= λ hole →
        prepareSource fr hole >>= λ result → ret (result , false))

  -- Step 4: every packed datum, checked against its closed type and
  -- audited. `names` is not empty.
  pack : Frame → Nat → List String → List Term → Leaves → Term → Term → TC Packed
  pack fr l names hints (leaves B′ C′ dB′ B-set′ dC′ C-set′ f′ A′) FB₀ FC₀ =
    let G₀ = packedContext fr l
        B₀ = elim G₀ (familyMotive l) names (leafOf B′)
        C₀ = elim G₀ (familyMotive l) names (leafOf C′)
        f₀ = elim G₀ (mapMotive (app C₀) (app B₀)) names (leafOf f′)
        A₀₀ = elim G₀ (familyOverMotive B₀ l) names (leafOf A′)
        A₀ = def (quote OverTotal) (v A₀₀ ∷ [])
        dB₀ = elim♭ G₀ (discreteMotive B₀) names (leafOf dB′)
        B-set₀ = elim G₀ (setMotive B₀) names (leafOf B-set′)
        dC₀ = elim♭ G₀ (discreteMotive C₀) names (leafOf dC′)
        C-set₀ = elim G₀ (setMotive C₀) names (leafOf C-set′)
        TB₀ = def (quote LocalTotal) (v B₀ ∷ v A₀ ∷ [])
        TC₀ = def (quote LocalTotal)
                (v C₀ ∷ v (def (quote Reindexed) (v f₀ ∷ v A₀ ∷ [])) ∷ [])
        leaf = def (quote lowering) []
        presB₀ = elim G₀ (presentationMotive (app FB₀) (app TB₀)) names leaf
        presC₀ = elim G₀ (presentationMotive (app FC₀) (app TC₀)) names leaf
        -- DiscreteOver {ℓ} {G} X, the context written out.
        discreteOver : Term → Term
        discreteOver X =
          def (quote DiscreteOver) (h (levelAt l) ∷ h G₀ ∷ v X ∷ [])
        audit : String → Term → Term → TC Term
        audit label type t =
          stage (primStringAppend "packing " label) >>= λ _ →
          auditPacked fr type t
    in
    audit "the context" (setAt l) G₀ >>= λ G →
    audit "its discreteness" (def (quote Discrete) (v G₀ ∷ [])) (packedDiscrete fr) >>= λ dG →
    audit "its decision procedure" (def (quote DecEq) (v G₀ ∷ [])) (decider names hints) >>= λ dec →
    audit "B" (over G₀ (familyMotive l)) B₀ >>= λ B →
    audit "C" (over G₀ (familyMotive l)) C₀ >>= λ C →
    audit "dB" (discreteOver B₀) dB₀ >>= λ dB →
    audit "B-set" (over G₀ (setMotive B₀)) B-set₀ >>= λ B-set →
    audit "dC" (discreteOver C₀) dC₀ >>= λ dC →
    audit "C-set" (over G₀ (setMotive C₀)) C-set₀ >>= λ C-set →
    audit "f" (over G₀ (mapMotive (app C₀) (app B₀))) f₀ >>= λ f →
    audit "A" (arrow (def (quote Σ) (v G₀ ∷ v B₀ ∷ [])) (setAt l)) A₀ >>= λ A →
    audit "FB" (over G₀ (familyMotive l)) FB₀ >>= λ FB →
    audit "FC" (over G₀ (familyMotive l)) FC₀ >>= λ FC →
    audit "the local total source of B" (over G₀ (familyMotive l)) TB₀ >>= λ TB →
    audit "the local total source of C" (over G₀ (familyMotive l)) TC₀ >>= λ TC″ →
    audit "the presentation of FB"
      (over G₀ (presentationMotive (app FB₀) (app TB₀))) presB₀ >>= λ presB →
    audit "the presentation of FC"
      (over G₀ (presentationMotive (app FC₀) (app TC₀))) presC₀ >>= λ presC →
    -- The four components of each presentation: an accessor of the library
    -- on audited terms, every argument written out.
    let part : Name → Term → Term → Term → Term
        part nm F T p = def nm (h (levelAt l) ∷ h G ∷ h F ∷ h T ∷ v p ∷ [])
        outB = part (quote Presented.out) FB TB presB
        inB = part (quote Presented.back) FB TB presB
        secB = part (quote Presented.section-law) FB TB presB
        retB = part (quote Presented.retraction-law) FB TB presB
        outC = part (quote Presented.out) FC TC″ presC
        inC = part (quote Presented.back) FC TC″ presC
        secC = part (quote Presented.section-law) FC TC″ presC
        retC = part (quote Presented.retraction-law) FC TC″ presC
    in
    ret (packed-data G dG dec B C dB B-set dC C-set f A
           FB FC outB inB secB retB outC inC secC retC presB presC)

  -- The whole payload of a completed capture, as syntax.
  payloadOf : Name → Term
  payloadOf seed = def (quote C.Output.whole-context) (v (def seed []) ∷ [])

  -- Steps 1 to 8, for both entry points. Returns the level of the diagram
  -- and the audited closed terms that the bundle was defined with. It is
  -- run under `guarded` by its two callers.
  generate : {@♭ ℓ : Level} → Name → Deciders → {@♭ B C : Set ℓ}
    → (@♭ dB : Discrete B) (@♭ B-set : IsSet B)
    → (@♭ dC : Discrete C) (@♭ C-set : IsSet C)
    → (@♭ f : C → B) (@♭ A : B → Set ℓ) → TC (Σ Nat (λ _ → Packed))
  generate {ℓ} n deciders {B} {C} dB B-set dC C-set f A =
    -- 1. The frame.
    frame >>= λ fr →
    let names = frameNames fr
        point = packedPoint fr
    in
    nonEmpty names >>= λ _ →
    -- 2. The two sources, as captures will store them.
    prepareSources fr f A >>= λ where
      (l , FB₀ , FC₀) →
        -- 3. The leaves and the decision procedures.
        prepareLeaves fr l dB B-set dC C-set f A >>= λ prepared →
        quoteDeciders fr deciders >>= λ given →
        countsAgree (length names) (length given) >>= λ _ →
        strengthen (length names) names given >>= λ hints →
        -- 4. Packing and audit.
        pack fr l names hints prepared FB₀ FC₀ >>= λ where
          (packed-data G′ dG′ dec′ B′ C′ dB′ B-set′ dC′ C-set′ f′ A′
             FB′ FC′ outB′ inB′ secB′ retB′ outC′ inC′ secC′ retC′
             presB′ presC′) →
            -- 5. The packed data at the point are the user's arguments.
            stage "first native check: the packed data against the arguments" >>= λ _ →
            unquoteTC {A = PackedDiagramOf dB B-set dC C-set f A}
              (con (quote packed)
                (v G′ ∷ v dG′ ∷ v dec′ ∷ v B′ ∷ v C′
                 ∷ v dB′ ∷ v B-set′ ∷ v dC′ ∷ v C-set′ ∷ v f′ ∷ v A′
                 ∷ v point ∷ v FB′ ∷ v FC′
                 ∷ v outB′ ∷ v inB′ ∷ v secB′ ∷ v retB′
                 ∷ v outC′ ∷ v inC′ ∷ v secC′ ∷ v retC′ ∷ [])) >>= λ _ →
            -- 6. The two captures.
            stage "the two captures" >>= λ _ →
            freshName "diagram-capture-B" >>= λ seedB →
            declareSeed {a = ℓ} {ℓ = ℓ} [] seedB (Σ B A) >>= λ _ →
            freshName "diagram-capture-C" >>= λ seedC →
            declareSeed {a = ℓ} {ℓ = ℓ} (def seedB [] ∷ []) seedC (Σ C (A ∘ f)) >>= λ _ →
            -- 7. The bundle.
            stage "the bundle" >>= λ _ →
            quoteTC (CapturedDiagram ℓ) >>= λ type →
            declareDef (inst n) type >>= λ _ →
            defineFun n (clause [] []
              (con (quote captured-diagram)
                (v G′ ∷ v dG′ ∷ v dec′ ∷ v B′ ∷ v C′
                 ∷ v dB′ ∷ v B-set′ ∷ v dC′ ∷ v C-set′ ∷ v f′ ∷ v A′
                 ∷ v point ∷ v FB′ ∷ v FC′
                 ∷ v (payloadOf seedB) ∷ v (payloadOf seedC)
                 ∷ v outB′ ∷ v inB′ ∷ v secB′ ∷ v retB′
                 ∷ v outC′ ∷ v inC′ ∷ v secC′ ∷ v retC′ ∷ [])) ∷ []) >>= λ _ →
            -- 8. The bundle against the user's arguments and the captures.
            stage "second native check: the bundle against the arguments and the captures" >>= λ _ →
            unquoteTC {A = CapturedShape {ℓ = ℓ} (Σ B A)} (def seedB []) >>= λ sB →
            unquoteTC {A = CapturedShape {ℓ = ℓ} (Σ C (A ∘ f))} (def seedC []) >>= λ sC →
            unquoteTC {A = CapturedDiagram ℓ} (def n []) >>= λ d →
            unquoteTC {A = CapturedDiagramOf dB B-set dC C-set f A sB sC d}
              (con (quote bundled) (v (def n []) ∷ [])) >>= λ _ →
            ret (l , packed-data G′ dG′ dec′ B′ C′ dB′ B-set′ dC′ C-set′ f′ A′
                       FB′ FC′ outB′ inB′ secB′ retB′ outC′ inC′ secC′ retC′
                       presB′ presC′)

declareCapturedDiagram : {@♭ ℓ : Level} → Name → Deciders → {@♭ B C : Set ℓ}
  → (@♭ dB : Discrete B) (@♭ B-set : IsSet B)
  → (@♭ dC : Discrete C) (@♭ C-set : IsSet C)
  → (@♭ f : C → B) (@♭ A : B → Set ℓ) → TC ⊤
declareCapturedDiagram n deciders dB B-set dC C-set f A = guarded (
  generate n deciders dB B-set dC C-set f A >>= λ _ → stage "done")

-- The same, and in the same call the DESCRIPTOR of the bundle for the
-- staged route to the empty context (step 9; DiagramMetadata,
-- ReadCapturedDiagram, STAGE-CAPTURED-DIAGRAM.txt):
--
--   unquoteDecl cells descriptor =
--     declareStagedDiagram cells descriptor (bool-dec ∷ code-dec b ∷ [])
--       dB B-set dC C-set f A
--
--   cells      : CapturedDiagram ℓ          as above, an instance
--   descriptor : CapturedDiagramFor m       descriptor = describe cells
--
-- where m is written out in the declared TYPE: meta-of applied to the
-- level and to the audited closed terms that `cells` was defined with
-- (the two presentation families themselves, where `cells` has their
-- four components each), every argument visible, no name of the module.
-- Agda checks the definition against that type, that is, m against the
-- metadata that the constructor reads off `cells`. The descriptor is an
-- ordinary definition and not an instance; nothing is looked up through
-- it, and it requests no shape.
declareStagedDiagram : {@♭ ℓ : Level} → Name → Name → Deciders
  → {@♭ B C : Set ℓ}
  → (@♭ dB : Discrete B) (@♭ B-set : IsSet B)
  → (@♭ dC : Discrete C) (@♭ C-set : IsSet C)
  → (@♭ f : C → B) (@♭ A : B → Set ℓ) → TC ⊤
declareStagedDiagram n s deciders dB B-set dC C-set f A = guarded (
  generate n deciders dB B-set dC C-set f A >>= λ where
    (l , packed-data G′ dG′ dec′ B′ C′ dB′ B-set′ dC′ C-set′ f′ A′
           FB′ FC′ _ _ _ _ _ _ _ _ presB′ presC′) →
      -- 9. The descriptor, with the closed metadata in its type.
      stage "the descriptor" >>= λ _ →
      declareDef (v s)
        (def (quote CapturedDiagramFor)
          (h (levelAt l)
           ∷ v (def (quote meta-of)
                 (v (levelAt l)
                  ∷ v G′ ∷ v dG′ ∷ v dec′ ∷ v B′ ∷ v C′
                  ∷ v dB′ ∷ v B-set′ ∷ v dC′ ∷ v C-set′ ∷ v f′ ∷ v A′
                  ∷ v FB′ ∷ v FC′ ∷ v presB′ ∷ v presC′ ∷ []))
           ∷ [])) >>= λ _ →
      defineFun s (clause [] []
        (con (quote describe) (v (def n []) ∷ [])) ∷ []) >>= λ _ →
      stage "done")
