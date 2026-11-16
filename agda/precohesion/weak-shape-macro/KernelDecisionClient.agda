{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Stage I4 at the kernel. Opus, 14 November 2026; opus-closed-limits-01
-- (delta 07). Nothing is postulated or declared. Inhabits Fable's
-- Kernel … Classifier.Attachments.Statement-I4 and Statement-I4′ with
-- AttachmentDecision.Decide, at G = Att.G V written through the alias
-- module AtV = Su.Att V (the route of attachment-conversion-diagnostic-01),
-- fed with the kernel's own C, C-set, bottom, truth-point, Tj, Tk and the
-- discreteness/sethood of cP V; c3 is ClosedEndpoints.c3-generic at the
-- kernel's own Su.Qd.
module KernelDecisionClient where

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
open import ClosedEndpoints using (c3-generic)
open import AttachmentDecision using (module Decide)
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

      c3 : Su.bottom ≡ Ke.Pr.truth-point → Su.P
      c3 = c3-generic fe-j pe-j Su.Qd.p Su.Qd.p-to-P refl refl

      module AtB = Su.Att B
      module AtB′ = Su.Att B′

      module AtAttachments
        (@♭ sU : ShapeData (Su.Att.U B))
        (@♭ sPow : ShapeData (ʃ sU → Su.Att.U B))
        (@♭ sSecH : ShapeData (ʃ sU → ♭ (Su.Att.U B)))
        (@♭ sSecS : ShapeData (ʃ sU → ʃ sU))
        (@♭ sU′ : ShapeData (Su.Att.U B′))
        (@♭ sPow′ : ShapeData (ʃ sU′ → Su.Att.U B′))
        (@♭ sSecH′ : ShapeData (ʃ sU′ → ♭ (Su.Att.U B′)))
        (@♭ sSecS′ : ShapeData (ʃ sU′ → ʃ sU′)) where

        module Ats = Cf.Attachments sU sPow sSecH sSecS sU′ sPow′ sSecH′ sSecS′

        module PoB = Pushout {lsuc i} {lsuc (lsuc i)} Qk Ek Ke.Tk
          {Dm = AtB.G} {Bt = AtB.G × AtB.G} (λ x → x , x)
          (sharp-unit Su.bottom) (sharp-unit Ke.Pr.truth-point)
        module BxB = BoxedCover {lsuc i} {lsuc (lsuc i)} fe-k Qk Ek Ke.Tk
          {Dm = AtB.G} {Bt = AtB.G × AtB.G} (λ x → x , x)
          (sharp-unit Su.bottom) (sharp-unit Ke.Pr.truth-point)
        module PoB′ = Pushout {lsuc i} {lsuc (lsuc i)} Qk Ek Ke.Tk
          {Dm = AtB′.G} {Bt = AtB′.G × AtB′.G} (λ x → x , x)
          (sharp-unit Su.bottom) (sharp-unit Ke.Pr.truth-point)
        module BxB′ = BoxedCover {lsuc i} {lsuc (lsuc i)} fe-k Qk Ek Ke.Tk
          {Dm = AtB′.G} {Bt = AtB′.G × AtB′.G} (λ x → x , x)
          (sharp-unit Su.bottom) (sharp-unit Ke.Pr.truth-point)

        module DB = Decide fe-j pe-j fe-k Ke.Tk Ke.Tj Su.P Ke.Pr.C
          Su.Cl.C-set Su.bottom Ke.Pr.truth-point c3
          AtB.G (Su.CP.cP-discrete dB) (Su.CP.cP-set {B})
          AtB.U AtB.At.end refl refl AtB.At.present AtB.At.attach
          (λ Y-set fA fD ag → PoB.Extend.extend Y-set fA fD ag)
          (λ Y-set fA fD ag → PoB.Extend.extend-vertex Y-set fA fD ag)
          (λ Y-set fA fD ag → PoB.Extend.extend-middle Y-set fA fD ag)
          BxB.boxed-cover sC sU

        module DB′ = Decide fe-j pe-j fe-k Ke.Tk Ke.Tj Su.P Ke.Pr.C
          Su.Cl.C-set Su.bottom Ke.Pr.truth-point c3
          AtB′.G (Su.CP.cP-discrete dB′) (Su.CP.cP-set {B′})
          AtB′.U AtB′.At.end refl refl AtB′.At.present AtB′.At.attach
          (λ Y-set fA fD ag → PoB′.Extend.extend Y-set fA fD ag)
          (λ Y-set fA fD ag → PoB′.Extend.extend-vertex Y-set fA fD ag)
          (λ Y-set fA fD ag → PoB′.Extend.extend-middle Y-set fA fD ag)
          BxB′.boxed-cover sC sU′

        i4 : Ats.Statement-I4
        i4 σ ct = DB.decision σ ct

        i4′ : Ats.Statement-I4′
        i4′ σ′ ct = DB′.decision σ′ ct
