{-# OPTIONS --cohesion --without-K --flat-split #-}

module CaptureFixtures where

-- This imported definition retains the crisp binder in Agda's owning
-- declaration. Reflection need only preserve the name and its arguments.
CrispArrow : (@♭ A B : Set) → Set
CrispArrow A B = (@♭ x : A) → B

module Parameterized (@♭ A : Set) where
  Alias : Set
  Alias = A

  data Wrapper : Set where
    wrap : A → Wrapper
