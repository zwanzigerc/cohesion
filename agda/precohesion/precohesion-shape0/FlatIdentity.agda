{-# OPTIONS --without-K --cohesion --flat-split #-}

module FlatIdentity where

open import Foundations

-- Isolated crisp identity induction, already used in the earlier project.
-- Agda 2.8 does not allow --safe together with --without-K --flat-split.
-- There are no postulates here.
box-identity : BoxIdentity
box-identity A x .x refl = refl
