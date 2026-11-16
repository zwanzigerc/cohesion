{-# OPTIONS --cohesion --without-K --flat-split #-}

-- At ONE level, IndexedParameter.Parameter is DiscreteParameters.Parameter.
-- Claude (Fable), 13 November 2026; after fable-impl-16 (HANDOFF-33 item 2).
-- Postulate-free; nothing but three equations, each by computation.
--
-- For the same crisp data with the index J at the level of the shape, the
-- two modules have the same recursor at a crisp index, the same recursor at
-- an ordinary index and the same unit law. Each pair is equal as terms, by
-- refl; the two unit laws have one type because the two recursors compute
-- to the same term.
--
-- This is a separate module so that IndexedParameter itself does not
-- import DiscreteParameters and, below it, CapturedShape and ShapeElim.
module IndexedParameterSameLevel where

open import Foundations
open import GlobalPrecohesion using (ShapeData)
import DiscreteParameters as Old
import IndexedParameter as New

module _
  {@♭ ℓ : Level}
  {@♭ X : Set ℓ} (@♭ s : ShapeData X)
  {@♭ J : Set ℓ} (@♭ J-discrete : Discrete J)
  (@♭ D : J → Set ℓ)
  (@♭ D-set : (u : J) → IsSet (D u))
  (@♭ D-discrete : (@♭ u : J) → Discrete (D u))
  (@♭ f : (u : J) → X → D u) where

  private
    module O = Old.Parameter s J-discrete D D-set D-discrete f
    module N = New.Parameter s J-discrete D D-set D-discrete f

  same-rec-at : (@♭ u : J) → N.rec-at u ≡ O.rec-at u
  same-rec-at u = refl

  same-rec-param : N.rec-param ≡ O.rec-param
  same-rec-param = refl

  same-rec-param-η : N.rec-param-η ≡ O.rec-param-η
  same-rec-param-η = refl
