{-# OPTIONS --cohesion --without-K --flat-split #-}

-- C4 at the two levels the set-source theorem uses. Opus, 14 November 2026;
-- opus-closed-limits-01 (delta 03). Nothing is postulated or declared.
--
--   AtO   IsSet (♯ (O i)) at level j = lsuc i, from BaseClassifierLaws.Laws
--         .O-is-set and FunExt₂ j j (the input of the support sO);
--   AtC   IsSet (♯ C) at level k = lsuc j, for the closed classifier C of
--         PrincipalFilter.Principal sX … Quantified … Closed, from its C-set
--         and FunExt₂ k k (fe-k of the kernel).
-- FunExt₂ ℓ ℓ is accepted where SharpPath.FunExtAt ℓ is asked (the two
-- unfold to the same type). The lemma itself is SharpSet (literally --safe).
module SharpSetExamples where

open import Foundations
open import NativeSharp using (♯)
open import GlobalPrecohesion using (ShapeData)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions using (PropExt)
open import BaseClassifier using (O)
open import BaseClassifierLaws using (module Laws)
open import PrincipalFilter using (module Principal)
open import SharpSet using (sharp-is-set)

module AtO {@♭ i : Level} (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (fe-j : FunExt₂ (lsuc i) (lsuc i)) where

  sharp-O-set : IsSet (♯ (O i))
  sharp-O-set = sharp-is-set fe-j (Laws.O-is-set fe-i pe-i)

module AtC {@♭ i : Level} (@♭ sX : ShapeData (♯ (O i)))
  (@♭ sQ : ShapeData (Principal.Q sX))
  (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  (@♭ sR : ShapeData (Principal.R sX))
  (@♭ pe-j : PropExt (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i)))
  (fe-k : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i))) where

  open Principal sX using (C)
  open Principal.Quantified.Closed sX sQ fe-i pe-i fe-j sR pe-j fe-jk
    using (C-set)

  sharp-C-set : IsSet (♯ C)
  sharp-C-set = sharp-is-set fe-k C-set
