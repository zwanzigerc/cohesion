{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Stage C5 at the kernel. Opus, 14 November 2026; opus-closed-limits-01
-- (delta 05). Nothing is postulated or declared. Inhabits Fable's
-- Kernel … Open.Classifier.Statement-C5 with ClosedClassifierContraction.C5,
-- fed ONLY with the kernel's own instances Su.Qd, Su.Cl, Su.Sp, Su.Cm (no
-- second copy of the support is formed; §13.1).
module KernelC5Client where

open import Foundations
open import NativeSharp using (♯; sharp-unit)
open import GlobalPrecohesion using (ShapeData)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions using (PropExt)
open import LargeTarget using (LargeOn)
open import BaseClassifier using (O)
open import RelativeSliceShape using (RelativeShapeOver)
open import SmallQuotient using (Quotients; Eliminates; Effective)
open import OrdinaryTruncation using (PropTruncation)
open import SetSourceKernelStatements using (module Kernel)
open import GlobalPrecohesion using (ʃ)
open import ClosedClassifierContraction using (module C5)

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
  (@♭ sO : ShapeData (♯ (O i)))
  (@♭ sQ : ShapeData (Kernel.Pr.Q fe-i fe-j fe-k fe-ij fe-jk pe-i pe-j Qj Ej
           effective-j Qk Ek B B′ dB dB′ B-set B′-set A A-set f K K′ sO))
  (@♭ sR : ShapeData (Kernel.Pr.R fe-i fe-j fe-k fe-ij fe-jk pe-i pe-j Qj Ej
           effective-j Qk Ek B B′ dB dB′ B-set B′-set A A-set f K K′ sO))
  (@♭ sE : ShapeData (Kernel.Pr.F fe-i fe-j fe-k fe-ij fe-jk pe-i pe-j Qj Ej
           effective-j Qk Ek B B′ dB dB′ B-set B′-set A A-set f K K′ sO → ♯ (O i)))
  (@♭ sYQ : ShapeData (♯ (Kernel.Pr.Q fe-i fe-j fe-k fe-ij fe-jk pe-i pe-j Qj Ej
           effective-j Qk Ek B B′ dB dB′ B-set B′-set A A-set f K K′ sO)))
  (@♭ cQ : LargeOn (lsuc (lsuc i)) sYQ)
  (@♭ sOj : ShapeData (♯ (O (lsuc i)))) where

  module Ke = Kernel fe-i fe-j fe-k fe-ij fe-jk pe-i pe-j Qj Ej effective-j
    Qk Ek B B′ dB dB′ B-set B′-set A A-set f K K′ sO
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

    module AtClassifier
      (@♭ sOO : ShapeData (♯ (O (lsuc i)) × ♯ (O (lsuc i))))
      (@♭ sC : ShapeData (♯ Su.C))
      (@♭ sLL : ShapeData (ʃ sC → ʃ sC)) where

      module Cf = Op.Classifier sOO sC sLL

      module Z5 = C5 fe-j pe-j Ke.Pr.C Su.Cl.C-discrete Ke.Pr.inclusion
        Ke.Pr.truth-point Su.Qd.p
        (λ c x → Su.Cl.implication (Ke.Pr.inclusion c) (snd c) (Su.Qd.p-to-P x))
        Su.Sp.closed-retraction Su.Sp.retracts Su.Sp.closed-retraction-top
        sOj sOO sC

      c5 : Cf.Statement-C5
      c5 mc pp ns = Z5.contractible (Su.Cm.Membership.membership mc) pp ns
