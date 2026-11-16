{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Recovery of dropped parameters WITHOUT Agda's parameter reconstruction.
-- Claude (Fable), 12 November 2026; see FABLE-IMPL-01.txt.
--
-- Reflected syntax omits the parameters of constructors, record projections
-- and projection-like functions and writes `unknown` for them. Agda can put
-- them back (withReconstructed), but in 2.9.0-rc3 that code aborts with an
-- internal error at Telescope.hs:767 on an over-applied projection-like
-- function: ReconstructParameters.reconstruct starts the tail loop of a
-- ProjectionView with the type of the WHOLE application. The defect is
-- reached through every reflection primitive when the reconstruction flag
-- is set, and through the types of imported constants, so no scan of the
-- visible syntax can rule it out (RECONSTRUCTION-AUDIT-01.txt).
--
-- This module never sets that flag. It asks the ordinary elaborator instead:
--
--   f {unknown} a rest        is probed as   reveal (f {unknown}) a rest
--   f {unknown}               is probed as   reveal (f {unknown})
--   c {unknown} fields        is probed as   use (c {unknown} fields) (λ x → x)
--
-- `reveal` and `use` are ordinary functions, so their implicit arguments are
-- kept in the elaborated term and are quoted back. For `reveal` the implicit
-- A is the declared principal type  D pars  of f; for `use` it is the
-- declared codomain  D pars  of c. The parameters are read off, written
-- explicitly, and the explicit term is what the caller audits and declares.
-- Agda checks explicit parameters against the inferred ones when that term
-- is elaborated, so a wrong read-back is a type error, never a wrong payload.
module CaptureExplicit where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Reflection as R
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)

-- The three probes. None of them is projection-like: no principal argument
-- has a data or record type.
reveal : ∀ {a b} {A : Set a} {B : A → Set b} → ((x : A) → B x) → (x : A) → B x
reveal f x = f x

reveal♭ : ∀ {@♭ a} {b} {@♭ A : Set a} {B : (@♭ x : A) → Set b}
        → ((@♭ x : A) → B x) → (@♭ x : A) → B x
reveal♭ f x = f x

use : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
use x k = k x

-- A term with its type written next to it.
typed : ∀ {a} (A : Set a) → A → A
typed A x = x

-- Every exported reflection program of the frontend runs under `guarded`
-- and checks its own preconditions; everything else is private (fable-impl-03,
-- FABLE-REVIEW-03.txt section 1). In this module the exported programs are
-- `guarded` itself and `explicit`; the passes it is made of are private.
-- An enclosing  withReconstructed true  would send inferType, checkType,
-- quoteTC, getType and getContext into the compiler's parameter
-- reconstruction, which aborts Agda 2.9.0-rc3 (FRONTEND-M1-AUDIT-01.txt §6;
-- confirmed by compilation, see CaptureAmbientFlags.agda). An enclosing
-- withNormalisation true  would unfold the probes below before their
-- implicit arguments can be read. Both flags are therefore fixed here,
-- before the first primitive of the entrypoint.
guarded : ∀ {a} {A : Set a} → TC A → TC A
guarded m = withNormalisation false (withReconstructed false m)

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

  _or_ : Bool → Bool → Bool
  true or _ = true
  false or b = b

  append : {A : Set} → List A → List A → List A
  append [] ys = ys
  append (x ∷ xs) ys = x ∷ append xs ys

  length : {A : Set} → List A → Nat
  length [] = zero
  length (_ ∷ xs) = suc (length xs)

  takeN : {A : Set} → Nat → List A → List A
  takeN zero _ = []
  takeN (suc n) [] = []
  takeN (suc n) (x ∷ xs) = x ∷ takeN n xs

  dropN : {A : Set} → Nat → List A → List A
  dropN zero xs = xs
  dropN (suc n) [] = []
  dropN (suc n) (_ ∷ xs) = dropN n xs

  -- Leading `unknown` arguments: the dropped parameters.
  leading : List (Arg Term) → Nat
  leading (arg _ unknown ∷ ts) = suc (leading ts)
  leading _ = zero

  data Mode : Set where
    ordinary crisp : Mode

  probeName : Mode → Name
  probeName ordinary = quote reveal
  probeName crisp = quote reveal♭

  -- Does the principal argument of f have to be crisp? Reflected argument
  -- information does not say, so the elaborator is asked, speculatively.
  attempt : Mode → Name → List (Arg Term) → TC (Maybe Mode)
  attempt m f pars = runSpeculative (catchTC
    (checkType (def (probeName m) (v (def f pars) ∷ [])) unknown >>= λ _ →
     ret (just m , false))
    (ret (nothing , false)))

  classify : Name → List (Arg Term) → TC Mode
  classify f pars = attempt ordinary f pars >>= λ where
    (just m) → ret m
    nothing → attempt crisp f pars >>= λ where
      (just m) → ret m
      nothing → typeError
        ( strErr "Automatic shape capture cannot recover the hidden parameters of "
        ∷ nameErr f
        ∷ strErr ": its principal argument is neither an ordinary nor a crisp argument of a fixed universe level."
        ∷ [])

  identity : Term
  identity = lam visible (abs "x" (var 0 []))

private
  mutual
    -- One round: wrap every application that still shows dropped parameters.
    wrap : Nat → Term → TC Term
    wrap zero _ = fail "Context capture exceeded its syntax-normalization limit."
    wrap (suc n) (def (quote reveal) (a ∷ b ∷ arg _ A ∷ B ∷ F ∷ arg _ x ∷ rest)) =
      wrap n A >>= λ A′ → wrap n x >>= λ x′ → wrapArgs n rest >>= λ rest′ →
      ret (def (quote reveal) (a ∷ b ∷ h A′ ∷ h unknown ∷ F ∷ v x′ ∷ rest′))
    wrap (suc n) (def (quote reveal♭) (a ∷ b ∷ arg _ A ∷ B ∷ F ∷ arg _ x ∷ rest)) =
      wrap n A >>= λ A′ → wrap n x >>= λ x′ → wrapArgs n rest >>= λ rest′ →
      ret (def (quote reveal♭) (a ∷ b ∷ h A′ ∷ h unknown ∷ F ∷ v x′ ∷ rest′))
    -- A probe without its principal argument: the function itself. The
    -- elaborator also produces this form, by contracting  λ x → reveal F x.
    wrap (suc n) (def (quote reveal) (a ∷ b ∷ arg _ A ∷ B ∷ F ∷ [])) =
      wrap n A >>= λ A′ → ret (def (quote reveal) (a ∷ b ∷ h A′ ∷ h unknown ∷ F ∷ []))
    wrap (suc n) (def (quote reveal♭) (a ∷ b ∷ arg _ A ∷ B ∷ F ∷ [])) =
      wrap n A >>= λ A′ → ret (def (quote reveal♭) (a ∷ b ∷ h A′ ∷ h unknown ∷ F ∷ []))
    wrap (suc n) (def (quote use) (a ∷ b ∷ arg _ A ∷ B ∷ arg _ (con c args) ∷ k ∷ [])) =
      wrap n A >>= λ A′ →
      wrapArgs n (dropN (leading args) args) >>= λ fields →
      ret (def (quote use) (a ∷ b ∷ h A′ ∷ B ∷
        v (con c (append (takeN (leading args) args) fields)) ∷ k ∷ []))
    wrap (suc n) (def f args) with leading args
    ... | zero = wrapArgs n args >>= λ as → ret (def f as)
    ... | suc np with dropN (suc np) args
    ...   | [] =
              classify f args >>= λ m →
              ret (def (probeName m) (v (def f args) ∷ []))
    ...   | arg _ x ∷ rest =
              classify f (takeN (suc np) args) >>= λ m →
              wrap n x >>= λ x′ → wrapArgs n rest >>= λ rest′ →
              ret (def (probeName m) (v (def f (takeN (suc np) args)) ∷ v x′ ∷ rest′))
    wrap (suc n) (con c args) with leading args
    ... | zero = wrapArgs n args >>= λ as → ret (con c as)
    ... | suc np =
            wrapArgs n (dropN (suc np) args) >>= λ fields →
            ret (def (quote use)
              (v (con c (append (takeN (suc np) args) fields)) ∷ v identity ∷ []))
    wrap (suc n) (var i args) = wrapArgs n args >>= λ as → ret (var i as)
    wrap (suc n) (lam vis (abs nm b)) = wrap n b >>= λ b′ → ret (lam vis (abs nm b′))
    wrap (suc n) (pi (arg i a) (abs nm b)) =
      wrap n a >>= λ a′ → wrap n b >>= λ b′ → ret (pi (arg i a′) (abs nm b′))
    wrap (suc n) (agda-sort (set l)) = wrap n l >>= λ l′ → ret (agda-sort (set l′))
    wrap (suc n) (agda-sort (prop l)) = wrap n l >>= λ l′ → ret (agda-sort (prop l′))
    wrap (suc n) t@(agda-sort _) = ret t
    wrap (suc n) t@(lit _) = ret t
    wrap (suc n) (meta _ _) =
      fail "Automatic shape capture requires a fully determined source and context."
    wrap (suc n) unknown = fail "Automatic shape capture cannot use unknown syntax."
    wrap (suc n) (pat-lam _ _) =
      fail "Automatic shape capture does not yet support pattern-lambda types."

    wrapArgs : Nat → List (Arg Term) → TC (List (Arg Term))
    wrapArgs n [] = ret []
    wrapArgs n (arg i t ∷ ts) =
      wrap n t >>= λ t′ → wrapArgs n ts >>= λ ts′ → ret (arg i t′ ∷ ts′)

  mutual
    -- Is there an application whose parameters are still unknown? The
    -- function part F and the codomain B of a probe are never looked at.
    bare : Nat → Term → Bool
    bare zero _ = true
    bare (suc n) (def (quote reveal) (_ ∷ _ ∷ arg _ A ∷ _ ∷ _ ∷ arg _ x ∷ rest)) =
      bare n A or (bare n x or bareArgs n rest)
    bare (suc n) (def (quote reveal♭) (_ ∷ _ ∷ arg _ A ∷ _ ∷ _ ∷ arg _ x ∷ rest)) =
      bare n A or (bare n x or bareArgs n rest)
    bare (suc n) (def (quote reveal) (_ ∷ _ ∷ arg _ A ∷ _ ∷ _ ∷ [])) = bare n A
    bare (suc n) (def (quote reveal♭) (_ ∷ _ ∷ arg _ A ∷ _ ∷ _ ∷ [])) = bare n A
    bare (suc n) (def (quote use) (_ ∷ _ ∷ arg _ A ∷ _ ∷ arg _ (con c args) ∷ _ ∷ [])) =
      bare n A or bareArgs n (dropN (leading args) args)
    bare (suc n) (def f args) with leading args
    ... | zero = bareArgs n args
    ... | suc _ = true
    bare (suc n) (con c args) with leading args
    ... | zero = bareArgs n args
    ... | suc _ = true
    bare (suc n) (var _ args) = bareArgs n args
    bare (suc n) (lam _ (abs _ b)) = bare n b
    bare (suc n) (pi (arg _ a) (abs _ b)) = bare n a or bare n b
    bare (suc n) (agda-sort (set l)) = bare n l
    bare (suc n) (agda-sort (prop l)) = bare n l
    bare (suc n) unknown = true
    bare (suc n) _ = false

    bareArgs : Nat → List (Arg Term) → Bool
    bareArgs n [] = false
    bareArgs n (arg _ t ∷ ts) = bare n t or bareArgs n ts

private
  -- Parameters from the revealed type  D pars: one for each placeholder,
  -- with the placeholder's argument information.
  fill : List (Arg Term) → List (Arg Term) → Maybe (List (Arg Term))
  fill [] _ = just []
  fill (_ ∷ _) [] = nothing
  fill (arg i _ ∷ ps) (arg _ d ∷ ds) with fill ps ds
  ... | just rest = just (arg i d ∷ rest)
  ... | nothing = nothing

  parameters : Name → List (Arg Term) → Term → TC (List (Arg Term))
  parameters f placeholders (def d dargs) with fill placeholders dargs
  ... | just ps = ret ps
  ... | nothing = typeError
    ( strErr "Automatic shape capture cannot recover the hidden parameters of "
    ∷ nameErr f ∷ strErr " from the type " ∷ termErr (def d dargs) ∷ [])
  parameters f _ t = typeError
    ( strErr "Automatic shape capture cannot recover the hidden parameters of "
    ∷ nameErr f ∷ strErr " from the type " ∷ termErr t ∷ [])

  -- The function part of a probe: f with its placeholders, possibly
  -- eta-expanded by the elaborator.
  headOf : Term → Maybe (Σ Name (λ _ → List (Arg Term)))
  headOf (def f pars) = just (f , pars)
  headOf (lam _ (abs _ (def f pars))) = just (f , takeN (leading pars) pars)
  headOf _ = nothing

  -- Argument information of the principal argument: that of the binder
  -- which follows the parameters in the type of f.
  principalInfo : Nat → Term → ArgInfo
  principalInfo zero (pi (arg i _) _) = i
  principalInfo (suc n) (pi _ (abs _ b)) = principalInfo n b
  principalInfo _ _ = arg-info visible (modality relevant quantity-ω)

private
  mutual
    -- Replace every probe by the application it stands for, parameters explicit.
    settle : Nat → Term → TC Term
    settle zero _ = fail "Context capture exceeded its syntax-normalization limit."
    settle (suc n) (def (quote reveal) (_ ∷ _ ∷ arg _ A ∷ _ ∷ arg _ F ∷ arg _ x ∷ rest)) =
      settleProbe n A F x rest
    settle (suc n) (def (quote reveal♭) (_ ∷ _ ∷ arg _ A ∷ _ ∷ arg _ F ∷ arg _ x ∷ rest)) =
      settleProbe n A F x rest
    settle (suc n) (def (quote reveal) (_ ∷ _ ∷ arg _ A ∷ _ ∷ arg _ F ∷ [])) =
      settleHead n A F
    settle (suc n) (def (quote reveal♭) (_ ∷ _ ∷ arg _ A ∷ _ ∷ arg _ F ∷ [])) =
      settleHead n A F
    settle (suc n) (def (quote use) (_ ∷ _ ∷ arg _ A ∷ _ ∷ arg _ (con c args) ∷ _ ∷ [])) =
      settle n A >>= λ A′ →
      parameters c (takeN (leading args) args) A′ >>= λ ps →
      settleArgs n (dropN (leading args) args) >>= λ fields →
      ret (con c (append ps fields))
    settle (suc n) (def f args) = settleArgs n args >>= λ as → ret (def f as)
    settle (suc n) (con c args) = settleArgs n args >>= λ as → ret (con c as)
    settle (suc n) (var i args) = settleArgs n args >>= λ as → ret (var i as)
    settle (suc n) (lam vis (abs nm b)) = settle n b >>= λ b′ → ret (lam vis (abs nm b′))
    settle (suc n) (pi (arg i a) (abs nm b)) =
      settle n a >>= λ a′ → settle n b >>= λ b′ → ret (pi (arg i a′) (abs nm b′))
    settle (suc n) (agda-sort (set l)) = settle n l >>= λ l′ → ret (agda-sort (set l′))
    settle (suc n) (agda-sort (prop l)) = settle n l >>= λ l′ → ret (agda-sort (prop l′))
    settle (suc n) t = ret t

    settleProbe : Nat → Term → Term → Term → List (Arg Term) → TC Term
    settleProbe n A F x rest with headOf F
    ... | nothing = typeError
      (strErr "Automatic shape capture met an unexpected probe: " ∷ termErr F ∷ [])
    ... | just (f , placeholders) =
      settle n A >>= λ A′ →
      parameters f placeholders A′ >>= λ ps →
      settle n x >>= λ x′ → settleArgs n rest >>= λ rest′ →
      getType f >>= λ T →
      ret (def f (append ps (arg (principalInfo (length placeholders) T) x′ ∷ rest′)))

    -- The function alone, for a probe without its principal argument.
    settleHead : Nat → Term → Term → TC Term
    settleHead n A F with headOf F
    ... | nothing = typeError
      (strErr "Automatic shape capture met an unexpected probe: " ∷ termErr F ∷ [])
    ... | just (f , placeholders) =
      settle n A >>= λ A′ →
      parameters f placeholders A′ >>= λ ps →
      ret (def f ps)

    settleArgs : Nat → List (Arg Term) → TC (List (Arg Term))
    settleArgs n [] = ret []
    settleArgs n (arg i t ∷ ts) =
      settle n t >>= λ t′ → settleArgs n ts >>= λ ts′ → ret (arg i t′ ∷ ts′)

  mutual
    hasMeta : Nat → Term → Bool
    hasMeta zero _ = true
    hasMeta (suc n) (meta _ _) = true
    hasMeta (suc n) (def _ args) = metaArgs n args
    hasMeta (suc n) (con _ args) = metaArgs n args
    hasMeta (suc n) (var _ args) = metaArgs n args
    hasMeta (suc n) (lam _ (abs _ b)) = hasMeta n b
    hasMeta (suc n) (pi (arg _ a) (abs _ b)) = hasMeta n a or hasMeta n b
    hasMeta (suc n) (agda-sort (set l)) = hasMeta n l
    hasMeta (suc n) (agda-sort (prop l)) = hasMeta n l
    hasMeta (suc n) _ = false

    metaArgs : Nat → List (Arg Term) → Bool
    metaArgs n [] = false
    metaArgs n (arg _ t ∷ ts) = hasMeta n t or metaArgs n ts

private
  -- checkType quotes its result before the constraints it postponed are
  -- woken, so the quoted term can show metavariables that are solved a
  -- moment later. Checking the quoted term once more substitutes them.
  settled : Nat → Term → Term → TC Term
  settled zero _ e = ret e
  settled (suc k) ty e with hasMeta 4096 e
  ... | false = ret e
  ... | true = noConstraints (checkType e ty) >>= settled k ty

  rounds : Nat → Term → Term → TC Term
  rounds zero _ _ =
    fail "Automatic shape capture could not make all hidden parameters explicit."
  rounds (suc k) ty w with bare 4096 w
  ... | false = settle 4096 w
  ... | true =
    wrap 4096 w >>= λ q →
    debugPrint "capture.explicit" 10 (strErr "probe: " ∷ termErr q ∷ []) >>= λ _ →
    noConstraints (checkType q ty) >>= settled 3 ty >>= λ e →
    debugPrint "capture.explicit" 10 (strErr "elaborated: " ∷ termErr e ∷ []) >>= λ _ →
    rounds k ty e

  -- The postcondition of `explicit`, enforced here and not left to callers.
  definite : Term → TC Term
  definite e with hasMeta 4096 e
  ... | false = ret e
  ... | true =
    fail "Automatic shape capture requires a fully determined source and context."

-- `explicit ty t`: t with every dropped parameter written out. `ty` is the
-- type of t (for a type t, its sort). t must be valid in the current context.
-- Metavariables that t still shows are substituted first. The result
-- contains no metavariable: a term that keeps one is refused here.
explicit : Term → Term → TC Term
explicit ty t = guarded (settled 3 ty t >>= rounds 64 ty >>= definite)
