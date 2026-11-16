{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A fixture for the tests of the direct generator (step S3b). Claude
-- (Fable), 13 November 2026. No postulate, no capture. It is in a module
-- of its own because the point of it is that it is IMPORTED: the pass
-- that prepares a term unfolds definitions of the file of the call and
-- leaves imported names as they are written.
module DirectGeneratorFixtures where

open import Foundations
open import Agda.Builtin.Bool
open import DecidableBase using (DecEq)
open import DependentContextFixtures using (Code; code-dec)

-- A decision procedure for Code b that is handed a point of Code b and
-- does not use it. As a value it is code-dec b. As a TERM,  code-dec-at b v
-- mentions v.
code-dec-at : (@♭ b : Bool) → Code b → DecEq (Code b)
code-dec-at b _ = code-dec b
