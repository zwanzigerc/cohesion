{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Stage O at the kernel: inhabits Statement-O1-X, Statement-O1-Y and
-- Statement-O2 of Fable's UNCHANGED SetSourceKernelStatements, at its exact
-- telescope (Kernel … Support … Open), with the generic proofs of
-- OpenPoints.O1 and OpenComparison.O2. Opus, 14 November 2026;
-- opus-closed-limits-01 (delta 03). Nothing is postulated or declared.
-- Exported certificates used to specialise O1: the sethood of the totals
-- X = Σ B A and Y = Σ B′ (A ∘ f) (TotalBridge.Σ-set of B-set, A-set).
module KernelOpenClient where

open import Foundations
open import NativeSharp using (♯)
open import GlobalPrecohesion using (ShapeData)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions using (PropExt)
open import LargeTarget using (LargeOn)
open import BaseClassifier using (O)
open import RelativeSliceShape using (RelativeShapeOver)
open import SmallQuotient using (Quotients; Eliminates; Effective)
open import TotalBridge using (Σ-set)
open import SetSourceKernelStatements using (module Kernel)
open import OpenPoints using (module O1)
open import OpenComparison using (module O2)

module AtKernel {@♭ i : Level}
  (@♭ fe-i : FunExt₂ i i) (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  (@♭ fe-k : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i)))
  (@♭ fe-ij : FunExt₂ i (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i)))
  (@♭ pe-i : PropExt i) (@♭ pe-j : PropExt (lsuc i))
  (@♭ Qj : Quotients (lsuc i)) (@♭ Ej : Eliminates Qj (lsuc i))
  (@♭ effective-j : Effective Qj)
  (@♭ Qk : Quotients (lsuc (lsuc i)))
  (@♭ Ek : Eliminates Qk (lsuc (lsuc i)))
  (@♭ B B′ : Set i) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ B-set : IsSet B) (@♭ B′-set : IsSet B′)
  (@♭ A : B → Set i) (@♭ A-set : (b : B) → IsSet (A b))
  (@♭ f : B′ → B)
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f))
  (@♭ sO : ShapeData (♯ (O i))) where

  module Ke = Kernel fe-i fe-j fe-k fe-ij fe-jk pe-i pe-j Qj Ej effective-j
    Qk Ek B B′ dB dB′ B-set B′-set A A-set f K K′ sO

  -- Certificates: the two totals are sets.
  X-set : IsSet Ke.X
  X-set = Σ-set B-set A-set

  Y-set : IsSet Ke.Y
  Y-set = Σ-set B′-set (λ b′ → A-set (f b′))

  module AtSupport
    (@♭ sQ : ShapeData Ke.Pr.Q) (@♭ sR : ShapeData Ke.Pr.R)
    (@♭ sE : ShapeData (Ke.Pr.F → ♯ (O i)))
    (@♭ sYQ : ShapeData (♯ Ke.Pr.Q))
    (@♭ cQ : LargeOn (lsuc (lsuc i)) sYQ)
    (@♭ sOj : ShapeData (♯ (O (lsuc i)))) where

    module Su = Ke.Support sQ sR sE sYQ cQ sOj

    module AtOpen
      (@♭ saX : ShapeData (♯ (♭ Ke.X)))
      (@♭ saaX : ShapeData (♯ (♭ Ke.X) × ♯ (♭ Ke.X)))
      (@♭ caaX : LargeOn (lsuc i) saaX) (@♭ cX : LargeOn (lsuc i) Ke.sX)
      (@♭ saY : ShapeData (♯ (♭ Ke.Y)))
      (@♭ saaY : ShapeData (♯ (♭ Ke.Y) × ♯ (♭ Ke.Y)))
      (@♭ caaY : LargeOn (lsuc i) saaY) (@♭ cY : LargeOn (lsuc i) Ke.sY)
      where

      module Op = Su.Open saX saaX caaX cX saY saaY caaY cY

      o1-X : Op.Statement-O1-X
      o1-X = O1.statement-O1 sO sQ fe-i pe-i fe-j X-set Ke.sX saX saaX caaX

      o1-Y : Op.Statement-O1-Y
      o1-Y = O1.statement-O1 sO sQ fe-i pe-i fe-j Y-set Ke.sY saY saaY caaY

      o2 : Op.Statement-O2
      o2 = O2.o2 fe-i B B′ dB dB′ B-set B′-set A f K K′
