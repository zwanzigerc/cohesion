{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Elimination out of a captured shape, stated in the context of the shape.
-- Claude (Fable), 11 November 2026.
--
-- For a captured shape s of A, a discrete set D in the same crisp context,
-- and f : A → D, the macro `shape-elim` produces
--
--   map      : carrier s → D
--   map-unit : (x : A) → map (unit s x) ≡ f x
--
-- It packs D and f over the captured context the way `shape` packs A, and
-- applies the whole-context universal property that s already carries.
-- Nothing is postulated here: the native part is ordinary Agda, and the
-- macro only writes a term that Agda then checks. In particular a target
-- or a map that is not uniform over the captured context is rejected by
-- the type checker, not by this file.
module ShapeElim where

open import Foundations
open import CaptureContext
open import CapturedShape using (CapturedShape)
import CapturedShape as C
import RelativeSliceShape as R
open import PullbackSetFibers using (transport; retract-set; fiber-fst-set)
open import DiscretePullback
  using (discrete-ind; counit-section-discrete; identity-discrete)
open import CaptureExplicit using (guarded)
open import Agda.Builtin.Reflection as Refl
  using (Term; Name; TC; Arg; arg; arg-info; visible; hidden; modality;
         relevant; quantity-ω; Pattern; Clause; clause; pat-lam; def; con;
         var; lam; abs; unknown; bindTC; returnTC; typeError; strErr;
         termErr; inferType; reduce; normalise; getContext; unify;
         freshName; withReduceDefs; primShowQName; Telescope)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _==_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using (String; primStringToList; primShowNat)
open import Agda.Builtin.Char using (Char; primCharEquality)

------------------------------------------------------------------------
-- Raising a target to the level of the captured context.

raise-map : {@♭ a b c e : Level} {A : Set a} {D : Set c}
          → (A → D) → Raise b A → Raise e D
raise-map f (raise x) = raise (f x)

raise-set : {@♭ a b : Level} {A : Set a} → IsSet A → IsSet (Raise b A)
raise-set = retract-set lower raise raise-lower

raise-discrete : {@♭ a b : Level} {@♭ A : Set a}
               → (@♭ da : Discrete A) → Discrete (Raise b A)
raise-discrete {b = b} {A = A} da = counit-section-discrete lift lift-section
  where
  lift : Raise b A → ♭ (Raise b A)
  lift (raise x) = flat-map raise (inverse da x)

  lift-section : (r : Raise b A) → counit (lift r) ≡ r
  lift-section (raise x) =
    flat-map-counit raise (inverse da x) ∙ ap raise (section da x)

------------------------------------------------------------------------
-- A family over a discrete base whose fibres over crisp points are
-- discrete has a discrete total space.

module SigmaDiscrete
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} (@♭ dΓ : Discrete Γ)
  {@♭ D : Γ → Set ℓ} (@♭ dD : (@♭ γ : Γ) → Discrete (D γ)) where

  LiftFiber : Σ Γ D → Set ℓ
  LiftFiber = Fiber (counit {A = Σ Γ D})

  at-point : (@♭ γ : Γ) → (d : D γ) → LiftFiber (γ , d)
  at-point γ = discrete-ind (dD γ) (λ d → LiftFiber (γ , d))
    (λ d → box (γ , d) , refl)

  at-base : (γ : Γ) → (d : D γ) → LiftFiber (γ , d)
  at-base = discrete-ind dΓ (λ γ → (d : D γ) → LiftFiber (γ , d)) at-point

  lift : Σ Γ D → ♭ (Σ Γ D)
  lift (γ , d) = fst (at-base γ d)

  lift-section : (z : Σ Γ D) → counit (lift z) ≡ z
  lift-section (γ , d) = snd (at-base γ d)

  discrete : Discrete (Σ Γ D)
  discrete = counit-section-discrete lift lift-section

------------------------------------------------------------------------
-- A fibre over a crisp point of a map between discrete types is discrete.
-- So the carrier of a captured shape is a discrete set, and can itself be
-- the target of an elimination.

module FiberDiscrete
  {@♭ ℓ : Level} {@♭ Γ S : Set ℓ}
  (@♭ dΓ : Discrete Γ) (@♭ dS : Discrete S)
  (@♭ p : S → Γ) (@♭ γ : Γ) where

  LiftFiber : Fiber p γ → Set ℓ
  LiftFiber = Fiber (counit {A = Fiber p γ})

  at-path : (@♭ z : S) → (e : p z ≡ γ) → LiftFiber (z , e)
  at-path z = discrete-ind (identity-discrete dΓ (p z) γ)
    (λ e → LiftFiber (z , e)) (λ e → box (z , e) , refl)

  at-point : (z : S) → (e : p z ≡ γ) → LiftFiber (z , e)
  at-point = discrete-ind dS (λ z → (e : p z ≡ γ) → LiftFiber (z , e)) at-path

  lift : Fiber p γ → ♭ (Fiber p γ)
  lift (z , e) = fst (at-point z e)

  lift-section : (w : Fiber p γ) → counit (lift w) ≡ w
  lift-section (z , e) = snd (at-point z e)

  discrete : Discrete (Fiber p γ)
  discrete = counit-section-discrete lift lift-section

carrier-discrete : {@♭ a ℓ : Level} {@♭ A : Set a}
                 → (@♭ s : CapturedShape {ℓ = ℓ} A)
                 → Discrete (C.Output.carrier s)
carrier-discrete s = FiberDiscrete.discrete
  (C.Output.context-discrete s)
  (R.Output.total-discrete (C.Output.whole-context s))
  (R.Output.projection (C.Output.whole-context s))
  (C.Output.point s)

------------------------------------------------------------------------
-- The recursor and its computation rule, for a target that is already a
-- family over the captured context.

module Elim
  {@♭ a ℓ : Level} {@♭ A : Set a}
  (@♭ s : CapturedShape {ℓ = ℓ} A)
  (@♭ D̂ : C.Output.context s → Set ℓ)
  (@♭ D̂-set : (γ : C.Output.context s) → IsSet (D̂ γ))
  (@♭ D̂-discrete : (@♭ γ : C.Output.context s) → Discrete (D̂ γ))
  (@♭ f̂ : (γ : C.Output.context s) → C.Output.family s γ → D̂ γ)
  where

  private
    K = C.Output.whole-context s

  Target : Set ℓ
  Target = Σ (C.Output.context s) D̂

  target-discrete : Discrete Target
  target-discrete = SigmaDiscrete.discrete (C.Output.context-discrete s) D̂-discrete

  target-set-fibers : R.SetFibers (fst {B = D̂})
  target-set-fibers γ = fiber-fst-set γ (D̂-set γ)

  total-map : R.MapOver (fst {B = C.Output.family s}) (fst {B = D̂})
  total-map = R.over-map (λ z → fst z , f̂ (fst z) (snd z)) (λ _ → refl)

  factored : R.MapOver (R.Output.projection K) (fst {B = D̂})
  factored = R.Output.factor K Target target-discrete fst target-set-fibers total-map

  rec : C.Output.carrier s → D̂ (C.Output.point s)
  rec (z , e) = transport D̂ (R.triangle factored z ∙ e) (snd (R.function factored z))

  rec-β : (x : A)
        → rec (C.Output.unit s x)
          ≡ f̂ (C.Output.point s) (C.Output.source-embed s x)
  rec-β x = ap
    (λ h → transport D̂
      (R.triangle h (C.Output.point s , C.Output.source-embed s x))
      (snd (R.function h (C.Output.point s , C.Output.source-embed s x))))
    (R.Output.factor-β K Target target-discrete fst target-set-fibers total-map)

------------------------------------------------------------------------
-- What the user sees.

record ShapeElim {@♭ a ℓ : Level} {d : Level} {@♭ A : Set a}
                 (@♭ s : CapturedShape {ℓ = ℓ} A)
                 {D : Set d} (f : A → D) : Set (a ⊔ ℓ ⊔ d) where
  field
    map : C.Output.carrier s → D
    map-unit : (x : A) → map (C.Output.unit s x) ≡ f x

build : {@♭ a ℓ : Level} {d : Level} {@♭ A : Set a}
      → (@♭ s : CapturedShape {ℓ = ℓ} A)
      → (@♭ D̂ : C.Output.context s → Set ℓ)
      → (@♭ D̂-set : (γ : C.Output.context s) → IsSet (D̂ γ))
      → (@♭ D̂-discrete : (@♭ γ : C.Output.context s) → Discrete (D̂ γ))
      → (@♭ f̂ : (γ : C.Output.context s) → C.Output.family s γ → D̂ γ)
      → {D : Set d} (f : A → D)
      → (out : D̂ (C.Output.point s) → D)
      → ((x : A) → out (f̂ (C.Output.point s) (C.Output.source-embed s x)) ≡ f x)
      → ShapeElim s f
build s D̂ D̂-set D̂-discrete f̂ f out compatible = record
  { map = λ z → out (E.rec z)
  ; map-unit = λ x → ap out (E.rec-β x) ∙ compatible x
  }
  where module E = Elim s D̂ D̂-set D̂-discrete f̂

------------------------------------------------------------------------
-- The macro.

private
  infixl 1 _>>=_
  _>>=_ = bindTC
  ret = returnTC

  v : {X : Set} → X → Arg X
  v = arg (arg-info visible (modality relevant quantity-ω))

  length : {X : Set} → List X → Nat
  length [] = zero
  length (_ ∷ xs) = suc (length xs)

  reverseOnto : {X : Set} → List X → List X → List X
  reverseOnto [] ys = ys
  reverseOnto (x ∷ xs) ys = reverseOnto xs (x ∷ ys)

  -- The current point of the captured context, as a pattern that rebinds
  -- every context variable. Index k−1 is the oldest variable, as in
  -- CaptureShape.point.
  pointPattern : Nat → Pattern
  pointPattern zero = Refl.con (quote end-at) []
  pointPattern (suc k) =
    Refl.con (quote pair) (v (Refl.var k) ∷ v (pointPattern k) ∷ [])

  -- Clause telescope: the context variables, oldest first, types left to Agda.
  rebinding : Telescope → Telescope
  rebinding [] = []
  rebinding ((name , _) ∷ rest) = (name , v unknown) ∷ rebinding rest

  -- λ { point-pattern → body }. Inside the clause the pattern variables
  -- have the de Bruijn indices of the context variables they shadow, so
  -- `body` is used exactly as it was quoted in the ambient context.
  over-context : Telescope → Term → Term
  over-context oldest-first body =
    pat-lam (clause (rebinding oldest-first)
                    (v (pointPattern (length oldest-first)) ∷ [])
                    body ∷ []) []

  -- Names of the current file. A transparent definition of the current
  -- module is unfolded before packing, because reflected syntax cannot
  -- re-instantiate the module parameters it hides. Only such names are
  -- unfolded: imported definitions stay folded.
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
  localName prefix n = prefixOf prefix (primStringToList (primShowQName n))

  cons-if : Bool → Name → List Name → List Name
  cons-if true n ns = n ∷ ns
  cons-if false _ ns = ns

  mutual
    locals : List Char → Term → List Name → List Name
    locals prefix (def n args) acc =
      cons-if (localName prefix n) n (localsArgs prefix args acc)
    locals prefix (con n args) acc = localsArgs prefix args acc
    locals prefix (var _ args) acc = localsArgs prefix args acc
    locals prefix (lam _ (abs _ t)) acc = locals prefix t acc
    locals prefix (Refl.pi (arg _ dom) (abs _ cod)) acc =
      locals prefix dom (locals prefix cod acc)
    locals _ _ acc = acc

    localsArgs : List Char → List (Arg Term) → List Name → List Name
    localsArgs _ [] acc = acc
    localsArgs prefix (arg _ t ∷ ts) acc =
      locals prefix t (localsArgs prefix ts acc)

  unfold-locals : Nat → List Char → Term → TC Term
  unfold-locals zero _ t = ret t
  unfold-locals (suc rounds) prefix t with locals prefix t []
  ... | [] = ret t
  ... | names@(_ ∷ _) =
    withReduceDefs (true , names) (normalise t) >>= unfold-locals rounds prefix

  -- The number of variables a macro-generated shape captured: the length of
  -- its context  CrispΣ A (λ x → …) … CrispUnitAt ℓ.
  lastArg : List (Arg Term) → Maybe Term
  lastArg [] = nothing
  lastArg (arg _ t ∷ []) = just t
  lastArg (_ ∷ t ∷ ts) = lastArg (t ∷ ts)

  telescopeLength : Nat → Term → Maybe Nat
  telescopeLength zero _ = nothing
  telescopeLength (suc fuel) (def (quote CrispUnitAt) _) = just zero
  telescopeLength (suc fuel) (def (quote CrispΣ) args) with lastArg args
  ... | just (lam _ (abs _ rest)) with telescopeLength fuel rest
  ...   | just n = just (suc n)
  ...   | nothing = nothing
  telescopeLength (suc fuel) (def (quote CrispΣ) args) | _ = nothing
  telescopeLength (suc fuel) _ = nothing

  -- The target and the map are packed over ALL variables in scope, so the
  -- macro has to be used where the shape was formed. This check only turns
  -- the commonest mistake into a readable message; a context of the right
  -- length but the wrong types is rejected by Agda when it checks the term.
  sameLength : Nat → Maybe Nat → TC ⊤
  sameLength here nothing = ret tt
  sameLength here (just captured) with here == captured
  ... | true = ret tt
  ... | false = typeError
    ( strErr "shape-elim must be used in the crisp context in which the shape was formed: the shape captured "
    ∷ strErr (primShowNat captured)
    ∷ strErr " variable(s), and "
    ∷ strErr (primShowNat here)
    ∷ strErr " are in scope here. A target or a map that depends on a further variable is not a family over the captured context. For a further ORDINARY variable the missing principle is that discrete sets form an exponential ideal, which is product preservation for shape; the shape schema does not assert it."
    ∷ [])

  checkContext : Nat → Term → TC ⊤
  checkContext here s =
    normalise (def (quote C.Output.context) (v s ∷ [])) >>= λ context →
    sameLength here (telescopeLength 1024 context)

  -- ℓ, s, D and f from the declared type ShapeElim {a} {ℓ} {d} {A} s {D} f.
  record Goal : Set where
    constructor goal
    field
      level shape-term target map-term : Term

  goalOf : Term → TC Goal
  goalOf (def (quote ShapeElim)
            (arg _ a ∷ arg _ ℓ ∷ arg _ d ∷ arg _ A ∷ arg _ s ∷ arg _ D ∷ arg _ f ∷ [])) =
    ret (goal ℓ s D f)
  goalOf t = typeError
    (strErr "Use shape-elim at an explicitly declared type ShapeElim s f." ∷ termErr t ∷ [])

  eliminateBody : Term → Term → Term → TC ⊤
  eliminateBody D-set D-discrete hole =
    getContext >>= λ newest-first →
    freshName "shape-elim" >>= λ probe →
    let prefix = rootPrefix (primStringToList (primShowQName probe))
        tel = reverseOnto newest-first []
    in
    inferType hole >>= reduce >>= goalOf >>= λ where
      (goal ℓ s D f) →
        checkContext (length tel) s >>= λ _ →
        unfold-locals 4 prefix D >>= λ D′ →
        unfold-locals 4 prefix D-set >>= λ D-set′ →
        unfold-locals 4 prefix D-discrete >>= λ D-discrete′ →
        unfold-locals 4 prefix f >>= λ f′ →
        unify hole (def (quote build)
          ( v s
          ∷ v (over-context tel (def (quote Raise) (v ℓ ∷ v D′ ∷ [])))
          ∷ v (over-context tel (def (quote raise-set) (v D-set′ ∷ [])))
          ∷ v (over-context tel (def (quote raise-discrete) (v D-discrete′ ∷ [])))
          ∷ v (over-context tel (def (quote raise-map) (v f′ ∷ [])))
          ∷ v f
          ∷ v (def (quote lower) [])
          ∷ v (lam visible (abs "x" (Refl.con (quote refl) [])))
          ∷ []))

-- The program behind the macro, for callers that wrap it (fable-impl-03).
-- It writes a term that Agda then checks and declares nothing; it fixes the
-- reflection flags itself, so a caller's withReconstructed or
-- withNormalisation does not reach its primitives.
eliminate : Term → Term → Term → TC ⊤
eliminate D-set D-discrete hole = guarded (eliminateBody D-set D-discrete hole)

macro
  -- e : ShapeElim s f
  -- e = shape-elim D-is-set D-is-discrete
  shape-elim : Term → Term → Term → TC ⊤
  shape-elim s f hole = eliminate s f hole
