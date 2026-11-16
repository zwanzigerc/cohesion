{-# OPTIONS --cohesion --without-K --flat-split #-}

-- SET-SOURCE STAGES I1 and I2: the attachment is a set pushout, and every
-- point of its flat merely has a boxed generator. Opus, 14 November 2026;
-- opus-closed-limits-01 (delta 04), implementing FABLE-PLAN-SET-SOURCE-01
-- §7.1–7.2 (SET-ATTACHMENT-AND-BOXED-COVER-01) on Fable's UNCHANGED
-- definition SetSourceKernelStatements.Attachment.
--
-- I1 (module Pushout; ORDINARY parameters, as Attachment takes them, plus
-- the eliminator E : Eliminates Q (a ⊔ t) at the attachment's OWN level):
--   extend, extend-vertex, extend-middle   for a set Y of level a ⊔ t, maps
--      fA on Bt × Bool and fD on Dm × Tag agreeing along the edges
--      (fA (m d , t) ≡ fD (d , end t)) extend to U with both unit laws;
--   generators-unique   two maps U → Y into a set agreeing on vertices and
--      on middles agree;
--   cover   every point is merely a generator (Representatives).
-- The respect proof is by induction on Closure (edge, same, back, chain)
-- inside the truncation recursor into the identity type of the set Y.
-- I2 (module BoxedCover; crisp structure, FunExtAt (a ⊔ t)):
--   boxed-cover : (v : ♭ U) → ∥ Fiber (flat-map present) v ∥
--   (CrispTruncationExamples.Boxed.boxed-cover at present and cover).
-- Nothing is postulated; no shape; no extensionality in I1.
module AttachmentFacts where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Foundations
open import TruncationDiscrete using (_⊎_; inl; inr)
open import ShapeChoice using (FunExtAt)
open import OrdinaryTruncation using (PropTruncation)
open import SmallQuotient using (Quotients; Eliminates)
open import QuotientTruncations using (module Representatives)
import CrispTruncationExamples as CTE
open import SetSourceKernelStatements
  using (module Attachment; Closure; edge; same; back; chain)

module Pushout {a t : Level}
  (Q : Quotients (a ⊔ t)) (E : Eliminates Q (a ⊔ t))
  (T : PropTruncation (a ⊔ t))
  {Dm Bt : Set a} (m : Dm → Bt) {Tag : Set t} (e₀ e₁ : Tag) where

  open Attachment Q T m e₀ e₁
  open PropTruncation T
  open Quotients Q using (/-set)

  U-set : IsSet U
  U-set = /-set

  module Extend {Y : Set (a ⊔ t)} (Y-set : IsSet Y)
    (fA : Bt × Bool → Y) (fD : Dm × Tag → Y)
    (agree : (d : Dm) (s : Bool) → fA (m d , s) ≡ fD (d , end s)) where

    on-sum : Presentation → Y
    on-sum (inl x) = fA x
    on-sum (inr y) = fD y

    on-edge : {l n : Presentation} → Edge l n → on-sum l ≡ on-sum n
    on-edge ((d , s) , p , q) =
      ap on-sum p ∙ agree d s ∙ sym (ap on-sum q)

    on-closure : {l n : Presentation} → Closure Edge l n → on-sum l ≡ on-sum n
    on-closure (edge e) = on-edge e
    on-closure same = refl
    on-closure (back c) = sym (on-closure c)
    on-closure (chain c c′) = on-closure c ∙ on-closure c′

    respects : (l n : Presentation) → ∥ Closure Edge l n ∥ → on-sum l ≡ on-sum n
    respects l n = ∥-rec (Y-set (on-sum l) (on-sum n)) on-closure

    extend : U → Y
    extend = Eliminates./-rec E Y-set on-sum respects

    extend-vertex : (s : Bool) (b : Bt) → extend (vertex s b) ≡ fA (b , s)
    extend-vertex s b = Eliminates./-rec-unit E Y-set on-sum respects (inl (b , s))

    extend-middle : (d : Dm) (z : Tag) → extend (middle d z) ≡ fD (d , z)
    extend-middle d z = Eliminates./-rec-unit E Y-set on-sum respects (inr (d , z))

  generators-unique : {Y : Set (a ⊔ t)} → IsSet Y → (u v : U → Y)
    → ((s : Bool) (b : Bt) → u (vertex s b) ≡ v (vertex s b))
    → ((d : Dm) (z : Tag) → u (middle d z) ≡ v (middle d z))
    → (x : U) → u x ≡ v x
  generators-unique Y-set u v on-vertex on-middle =
    Eliminates./-unique E Y-set u v on-both
    where
    on-both : (l : Presentation) → u (present l) ≡ v (present l)
    on-both (inl (b , s)) = on-vertex s b
    on-both (inr (d , z)) = on-middle d z

  cover : (x : U) → ∥ Fiber present x ∥
  cover = Representatives.representative Q E T

module BoxedCover {@♭ a t : Level} (@♭ fe : FunExtAt (a ⊔ t))
  (@♭ Q : Quotients (a ⊔ t)) (@♭ E : Eliminates Q (a ⊔ t))
  (@♭ T : PropTruncation (a ⊔ t))
  {@♭ Dm Bt : Set a} (@♭ m : Dm → Bt) {@♭ Tag : Set t} (@♭ e₀ e₁ : Tag) where

  open Attachment Q T m e₀ e₁
  open PropTruncation T
  private
    module Po = Pushout Q E T m e₀ e₁

  boxed-cover : (v : ♭ U) → ∥ Fiber (flat-map present) v ∥
  boxed-cover = CTE.Boxed.boxed-cover fe T present Po.cover
