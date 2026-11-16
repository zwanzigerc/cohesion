{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Stages C3, I1, I2 at the kernel. Opus, 14 November 2026;
-- opus-closed-limits-01 (delta 04). Nothing is postulated or declared.
-- At Fable's UNCHANGED Kernel … Support telescope:
--   c3       : Su.bottom ≡ truth-point → Su.P     (the kernel's own bottom)
--   for each crisp V, at Su.Att V (U = the attachment of the diagonal of
--   cP V, at levels (j , k), quotient Qk with its own eliminator Ek, Tk):
--     extend / extend-vertex / extend-middle / generators-unique / cover (I1)
--     boxed-cover (I2, crisp, fe-k).
module KernelAttachmentClient where

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
open import ClosedEndpoints using (c3-generic)
open import AttachmentFacts using (module Pushout; module BoxedCover)

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

  c3 : Su.bottom ≡ Ke.Pr.truth-point → Su.P
  c3 = c3-generic fe-j pe-j Su.Qd.p Su.Qd.p-to-P refl refl

  module AtBase (@♭ V : Set i) where

    module Po = Pushout {lsuc i} {lsuc (lsuc i)} Qk Ek Ke.Tk
      {Dm = Su.Att.G V} {Bt = Su.Att.G V × Su.Att.G V} (λ x → x , x)
      (sharp-unit Su.bottom) (sharp-unit Ke.Pr.truth-point)

    module Bx = BoxedCover {lsuc i} {lsuc (lsuc i)} fe-k Qk Ek Ke.Tk
      {Dm = Su.Att.G V} {Bt = Su.Att.G V × Su.Att.G V} (λ x → x , x)
      (sharp-unit Su.bottom) (sharp-unit Ke.Pr.truth-point)

    -- The instances are formed at exactly the kernel's arguments (the
    -- attachment of Su.Att V). Their statements are NOT restated through the
    -- kernel's own copy Su.Att.At: comparing the two copies of Attachment
    -- reaches the closed proof inside `bottom` and stalls the compiler
    -- (FABLE-PLAN-SET-SOURCE-01 §13.1). Later stages use these instances.
    U-set = Po.U-set
    cover = Po.cover
    boxed-cover = Bx.boxed-cover
