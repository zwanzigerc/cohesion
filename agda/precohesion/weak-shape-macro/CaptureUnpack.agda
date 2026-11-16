{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Eliminators for a CRISP packed point. Claude (Fable), 13 November 2026;
-- fable-impl-11. Postulate-free; two definitions by matching on the
-- constructors of CaptureContext. No capture, closure, registration or
-- matching code is touched: CaptureContext itself is unchanged.
--
-- Packed data over a telescope are functions out of a packed point. The
-- existing eliminators take the packed point ORDINARILY:
--   unpack            non-dependent motive
--   unpack-dependent  motive over an ordinary packed point
-- The tail of a packed point is crisp, so every INNER step of a dependent
-- elimination has a motive over a crisp packed point. That is what these
-- two are for:
--   unpack-crisp      (P : (@♭ z : CrispΣ A B) → Set c)
--   unpack-end-crisp  (P : (@♭ u : CrispUnitAt ℓ) → Set c)
-- Native facts behind them (plan probes of fable-plan-automatic-assembly-01,
-- AssemblyEtaTail.agda.fail): a function with an ordinary domain is not
-- accepted where a function with a crisp domain is expected, so an inner
-- tail has to be eliminated by a combinator whose own type has the crisp
-- binder. Reflected syntax cannot write that annotation; a frontend gets
-- it from the expected type, as it already does for captured families.
module CaptureUnpack where

open import Foundations
open import CaptureContext using (CrispΣ; pair; CrispUnitAt; end-at; unpack-dependent)

unpack-crisp : {@♭ a b : Level} {c : Level}
             → {@♭ A : Set a} {@♭ B : (@♭ x : A) → Set b}
             → (P : (@♭ z : CrispΣ A B) → Set c)
             → ((@♭ x : A) → (@♭ tail : B x) → P (pair x tail))
             → (@♭ z : CrispΣ A B) → P z
unpack-crisp P k (pair x tail) = k x tail

unpack-end-crisp : {@♭ ℓ : Level} {c : Level}
                 → (P : (@♭ u : CrispUnitAt ℓ) → Set c)
                 → P end-at → (@♭ u : CrispUnitAt ℓ) → P u
unpack-end-crisp P k end-at = k

-- Step S3b, 13 November 2026: the constructor `pair` as a FUNCTION, for
-- the direct generator (DeclareCapturedDiagram). In a nest of the
-- eliminators above the motive of an inner step is the outer motive at
-- pair x tail. Agda's internal syntax drops the parameters of a
-- constructor, so a generated term that wrote the constructor there would
-- need them recovered at every level of every datum (CaptureExplicit).
-- An ordinary function keeps its arguments. It is the constructor by
-- computation, and the eliminators reduce on it.
paired : {@♭ a b : Level} {@♭ A : Set a} {@♭ B : (@♭ x : A) → Set b}
       → (@♭ x : A) (@♭ tail : B x) → CrispΣ A B
paired x tail = pair x tail

-- The two eliminators of a nonempty packed context with its two
-- parameters as EXPLICIT arguments, for the outermost step of a generated
-- nest. Reflected syntax gives arguments by position, so a generated term
-- can state A and B of unpack-dependent only after placeholders for the
-- three levels before them; here it states them and nothing else. A nest
-- that begins with one of these determines the types of all its bound
-- variables by itself, whatever its leaf mentions.
unpack-dependent-over : {@♭ a b : Level} {c : Level}
  → (@♭ A : Set a) (@♭ B : (@♭ x : A) → Set b)
  → (C : CrispΣ A B → Set c)
  → ((@♭ x : A) → (@♭ tail : B x) → C (pair x tail))
  → (z : CrispΣ A B) → C z
unpack-dependent-over A B = unpack-dependent

unpack-crisp-over : {@♭ a b : Level} {c : Level}
  → (@♭ A : Set a) (@♭ B : (@♭ x : A) → Set b)
  → (P : (@♭ z : CrispΣ A B) → Set c)
  → ((@♭ x : A) → (@♭ tail : B x) → P (pair x tail))
  → (@♭ z : CrispΣ A B) → P z
unpack-crisp-over A B = unpack-crisp
