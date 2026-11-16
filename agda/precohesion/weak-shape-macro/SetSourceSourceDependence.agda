{-# OPTIONS --cohesion --without-K --flat-split --lossy-unification #-}

-- WHICH ORDINARY STRUCTURE THE SOURCES OF THE 21 CHOICES DEPEND ON: a
-- native check.
-- Claude (Fable), 14 November 2026; fable-impl-23
-- (SET-SOURCE-PLAN-ASTRA-RELEASE-01: "check the exact set of closed
-- ordinary constants in its sources").
--
-- The kernel of the set-source theorem takes twelve ordinary structure
-- parameters: function extensionality at five pairs of levels,
-- propositional extensionality at two, the quotients at j and k with
-- their eliminators, effectivity at j. A module application passes ALL of
-- them to every definition, so the syntactic closure of a source reaches
-- all twelve, and says nothing about which of them the source depends on.
-- Here the kernel is applied TWICE in one context, at two sets of
-- parameters, and the sources are compared by conversion (refl), or the
-- second application is given the shapes and certificates of the first,
-- which it accepts only if the source types agree.
--
--   1 AllTwelve         Shapes and certificates are variables; all twelve
--                       parameters are varied. The sources of choices 1
--                       to 13 (support, open part, closed classifier) and
--                       the types of the five certificates are the same.
--   2 NotThree          Shapes are variables; effectivity at j and
--                       extensionality at (k,k) and at (i,j) are varied.
--                       The attachment of a closed base is the same, and
--                       the eight shapes of choices 14 to 21 are accepted
--                       at both.
--   3 BridgesAllTwelve  Shapes formed as the client forms them, by
--                       Bridge.data-of at closed relative shapes and by
--                       `attach`. Varied: all twelve, the bridging
--                       extensionalities at j and k, and the payload part
--                       of the diagram (the family, its sets, the two
--                       payloads). Q, R, F, the support P and the
--                       classifier C are the same.
--   4 BridgesNotThree   The same for the attachment. Varied: the three of
--                       2, the bridging extensionality at k and the
--                       payload part. Shared: the other nine and the
--                       bridging extensionality at j. The false endpoint,
--                       the closed reflection of a base and the
--                       attachment are the same.
--   5 BridgeCarrier     Carrier and unit of Bridge.data-of do not depend
--                       on its extensionality (for the powers, whose
--                       exponent is the carrier of a declared shape).
--
-- CONSEQUENCE for the client, where every parameter is a constant of
-- SetSourceFoundation and one constant serves in several roles (fe₁₁ is
-- the kernel's extensionality at (j,j) and the bridge of the shapes of
-- level j). Up to conversion:
--   choices 1 to 6 and 11 to 13   no ordinary constant;
--   choices 7 to 10               truncation₀ only: they are formed from
--                                 X = Σ B A and Y = Σ B′ (A ∘ f) (the
--                                 statement file, by definition) at the
--                                 truncated family;
--   choices 14 to 21              at most nine: Q₁, E₁, Q₂, E₂, fe₀₀,
--                                 fe₁₁, fe₁₂, pe₀, pe₁. effective₁, fe₂₂,
--                                 fe₀₁ and truncation₀ do not enter.
-- These are UPPER bounds: that each of the nine is needed is not shown.
-- NOT CHECKED: 4 with the bridging extensionality at j varied as well.
-- That comparison did not finish in 240 seconds (already the
-- discreteness of P at two bridges did not finish in 100). Nothing above
-- depends on it, fe₁₁ being among the nine.
--
-- THE OPTION --lossy-unification. With it the checker, comparing f a
-- with f b, first compares a with b; a success is a conversion by
-- congruence, and an accepted term is type-correct as always. Without
-- it, 1 is accepted as it stands (about 17 seconds) and 2 did not finish
-- in 400 seconds: the two instantiations are then unfolded and compared
-- through every proof term of the relations. No other module of the tree
-- uses the option.
--
-- All data are variables. Nothing is declared, and no statement of the
-- theorem is proved.
module SetSourceSourceDependence where

open import Foundations
open import NativeSharp using (♯)
open import GlobalPrecohesion using (ShapeData; ʃ; η; Closed)
open import ClosedBridge using (module Bridge)
open import ShapeChoice using (FunExtAt)
open import LargeTargetDeclare using (ClosedLargeUP; attach)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions using (PropExt)
open import LargeTarget using (LargeOn)
open import BaseClassifier using (O)
open import RelativeSliceShape
open import SmallQuotient
import SetSourceKernelStatements as Statements

------------------------------------------------------------------------
-- 1. All twelve varied: choices 1 to 13 and the five certificates.

module AllTwelve {@♭ i : Level}
  (@♭ fe-i : FunExt₂ i i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  (@♭ fe-k : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i)))
  (@♭ fe-ij : FunExt₂ i (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i)))
  (@♭ pe-i : PropExt i)
  (@♭ pe-j : PropExt (lsuc i))
  (@♭ Qj : Quotients (lsuc i))
  (@♭ Ej : Eliminates Qj (lsuc i))
  (@♭ effective-j : Effective Qj)
  (@♭ Qk : Quotients (lsuc (lsuc i)))
  (@♭ Ek : Eliminates Qk (lsuc (lsuc i)))
  (@♭ fe-i′ : FunExt₂ i i)
  (@♭ fe-j′ : FunExt₂ (lsuc i) (lsuc i))
  (@♭ fe-k′ : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i)))
  (@♭ fe-ij′ : FunExt₂ i (lsuc i))
  (@♭ fe-jk′ : FunExt₂ (lsuc i) (lsuc (lsuc i)))
  (@♭ pe-i′ : PropExt i)
  (@♭ pe-j′ : PropExt (lsuc i))
  (@♭ Qj′ : Quotients (lsuc i))
  (@♭ Ej′ : Eliminates Qj′ (lsuc i))
  (@♭ effective-j′ : Effective Qj′)
  (@♭ Qk′ : Quotients (lsuc (lsuc i)))
  (@♭ Ek′ : Eliminates Qk′ (lsuc (lsuc i)))
  (@♭ B B′ : Set i) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ B-set : IsSet B) (@♭ B′-set : IsSet B′)
  (@♭ A : B → Set i) (@♭ A-set : (b : B) → IsSet (A b))
  (@♭ f : B′ → B)
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f))
  (@♭ sO : ShapeData (♯ (O i)))
  where

  module M = Statements.Kernel
    fe-i fe-j fe-k fe-ij fe-jk pe-i pe-j Qj Ej effective-j Qk Ek
    B B′ dB dB′ B-set B′-set A A-set f K K′ sO
  module N = Statements.Kernel
    fe-i′ fe-j′ fe-k′ fe-ij′ fe-jk′ pe-i′ pe-j′ Qj′ Ej′ effective-j′ Qk′ Ek′
    B B′ dB dB′ B-set B′-set A A-set f K K′ sO

  -- The sources of the support (choices 2 to 5), and X and Y.
  Q-same : M.Pr.Q ≡ N.Pr.Q
  Q-same = refl

  R-same : M.Pr.R ≡ N.Pr.R
  R-same = refl

  F-same : M.Pr.F ≡ N.Pr.F
  F-same = refl

  X-same : M.X ≡ N.X
  X-same = refl

  Y-same : M.Y ≡ N.Y
  Y-same = refl

  module Support
    (@♭ sQ : ShapeData M.Pr.Q) (@♭ sR : ShapeData M.Pr.R)
    (@♭ sE : ShapeData (M.Pr.F → ♯ (O i)))
    (@♭ sYQ : ShapeData (♯ M.Pr.Q))
    (@♭ cQ : LargeOn (lsuc (lsuc i)) sYQ)
    (@♭ sOj : ShapeData (♯ (O (lsuc i))))
    where

    -- The second application is the test: the same five shapes and the
    -- same certificate are accepted at the other parameters.
    module M2 = M.Support sQ sR sE sYQ cQ sOj
    module N2 = N.Support sQ sR sE sYQ cQ sOj

    P-same : M2.P ≡ N2.P
    P-same = refl

    C-same : M2.C ≡ N2.C
    C-same = refl

    module Open
      (@♭ saX : ShapeData (♯ (♭ M.X)))
      (@♭ saaX : ShapeData (♯ (♭ M.X) × ♯ (♭ M.X)))
      (@♭ caaX : LargeOn (lsuc i) saaX) (@♭ cX : LargeOn (lsuc i) M.sX)
      (@♭ saY : ShapeData (♯ (♭ M.Y)))
      (@♭ saaY : ShapeData (♯ (♭ M.Y) × ♯ (♭ M.Y)))
      (@♭ caaY : LargeOn (lsuc i) saaY) (@♭ cY : LargeOn (lsuc i) M.sY)
      where

      -- cX and cY are certificates of the shape data of the totals at
      -- BOTH sets of parameters: carrier and unit do not depend on them.
      module M3 = M2.Open saX saaX caaX cX saY saaY caaY cY
      module N3 = N2.Open saX saaX caaX cX saY saaY caaY cY

      module Classifier
        (@♭ sOO : ShapeData (♯ (O (lsuc i)) × ♯ (O (lsuc i))))
        (@♭ sC : ShapeData (♯ M2.C))
        (@♭ sLL : ShapeData (ʃ sC → ʃ sC))
        where

        module M4 = M3.Classifier sOO sC sLL
        module N4 = N3.Classifier sOO sC sLL

------------------------------------------------------------------------
-- 2. Three varied, through to the attachments: choices 14 to 21.
--    Effectivity at j and extensionality at (k,k) and at (i,j) are
--    varied; the other nine parameters are shared.

module NotThree {@♭ i : Level}
  (@♭ fe-i : FunExt₂ i i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  (@♭ fe-k : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i)))
  (@♭ fe-ij : FunExt₂ i (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i)))
  (@♭ pe-i : PropExt i)
  (@♭ pe-j : PropExt (lsuc i))
  (@♭ Qj : Quotients (lsuc i))
  (@♭ Ej : Eliminates Qj (lsuc i))
  (@♭ effective-j : Effective Qj)
  (@♭ Qk : Quotients (lsuc (lsuc i)))
  (@♭ Ek : Eliminates Qk (lsuc (lsuc i)))
  (@♭ fe-k′ : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i)))
  (@♭ fe-ij′ : FunExt₂ i (lsuc i))
  (@♭ effective-j′ : Effective Qj)
  (@♭ B B′ : Set i) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ B-set : IsSet B) (@♭ B′-set : IsSet B′)
  (@♭ A : B → Set i) (@♭ A-set : (b : B) → IsSet (A b))
  (@♭ f : B′ → B)
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f))
  (@♭ sO : ShapeData (♯ (O i)))
  where

  module M = Statements.Kernel
    fe-i fe-j fe-k fe-ij fe-jk pe-i pe-j Qj Ej effective-j Qk Ek
    B B′ dB dB′ B-set B′-set A A-set f K K′ sO
  module N = Statements.Kernel
    fe-i fe-j fe-k′ fe-ij′ fe-jk pe-i pe-j Qj Ej effective-j′ Qk Ek
    B B′ dB dB′ B-set B′-set A A-set f K K′ sO

  module Support
    (@♭ sQ : ShapeData M.Pr.Q) (@♭ sR : ShapeData M.Pr.R)
    (@♭ sE : ShapeData (M.Pr.F → ♯ (O i)))
    (@♭ sYQ : ShapeData (♯ M.Pr.Q))
    (@♭ cQ : LargeOn (lsuc (lsuc i)) sYQ)
    (@♭ sOj : ShapeData (♯ (O (lsuc i))))
    where

    module M2 = M.Support sQ sR sE sYQ cQ sOj
    module N2 = N.Support sQ sR sE sYQ cQ sOj

    -- The closed reflection of a base and its attachment, directly.
    closed-base-same : (@♭ V : Set i) → M2.Att.G V ≡ N2.Att.G V
    closed-base-same V = refl

    attachment-same : (@♭ V : Set i) → M2.Att.U V ≡ N2.Att.U V
    attachment-same V = refl

    module Open
      (@♭ saX : ShapeData (♯ (♭ M.X)))
      (@♭ saaX : ShapeData (♯ (♭ M.X) × ♯ (♭ M.X)))
      (@♭ caaX : LargeOn (lsuc i) saaX) (@♭ cX : LargeOn (lsuc i) M.sX)
      (@♭ saY : ShapeData (♯ (♭ M.Y)))
      (@♭ saaY : ShapeData (♯ (♭ M.Y) × ♯ (♭ M.Y)))
      (@♭ caaY : LargeOn (lsuc i) saaY) (@♭ cY : LargeOn (lsuc i) M.sY)
      where

      module M3 = M2.Open saX saaX caaX cX saY saaY caaY cY
      module N3 = N2.Open saX saaX caaX cX saY saaY caaY cY

      module Classifier
        (@♭ sOO : ShapeData (♯ (O (lsuc i)) × ♯ (O (lsuc i))))
        (@♭ sC : ShapeData (♯ M2.C))
        (@♭ sLL : ShapeData (ʃ sC → ʃ sC))
        where

        module M4 = M3.Classifier sOO sC sLL
        module N4 = N3.Classifier sOO sC sLL

        module Attachments
          (@♭ sU : ShapeData (M2.Att.U B))
          (@♭ sPow : ShapeData (ʃ sU → M2.Att.U B))
          (@♭ sSecH : ShapeData (ʃ sU → ♭ (M2.Att.U B)))
          (@♭ sSecS : ShapeData (ʃ sU → ʃ sU))
          (@♭ sU′ : ShapeData (M2.Att.U B′))
          (@♭ sPow′ : ShapeData (ʃ sU′ → M2.Att.U B′))
          (@♭ sSecH′ : ShapeData (ʃ sU′ → ♭ (M2.Att.U B′)))
          (@♭ sSecS′ : ShapeData (ʃ sU′ → ʃ sU′))
          where

          -- The same eight shapes are accepted at the other parameters.
          module M5 = M4.Attachments sU sPow sSecH sSecS
            sU′ sPow′ sSecH′ sSecS′
          module N5 = N4.Attachments sU sPow sSecH sSecS
            sU′ sPow′ sSecH′ sSecS′

------------------------------------------------------------------------
-- 3. The shapes formed as the client forms them: Bridge.data-of at
--    closed relative shapes, with an extensionality of the level, and
--    `attach` for the certificate. Varied here: all twelve parameters,
--    the four bridging extensionalities, and the whole payload part of
--    the diagram (the family, its sets, both payloads).

module BridgesAllTwelve {@♭ i : Level}
  (@♭ fe-i : FunExt₂ i i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  (@♭ fe-k : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i)))
  (@♭ fe-ij : FunExt₂ i (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i)))
  (@♭ pe-i : PropExt i)
  (@♭ pe-j : PropExt (lsuc i))
  (@♭ Qj : Quotients (lsuc i))
  (@♭ Ej : Eliminates Qj (lsuc i))
  (@♭ effective-j : Effective Qj)
  (@♭ Qk : Quotients (lsuc (lsuc i)))
  (@♭ Ek : Eliminates Qk (lsuc (lsuc i)))
  (@♭ fe-i′ : FunExt₂ i i)
  (@♭ fe-j′ : FunExt₂ (lsuc i) (lsuc i))
  (@♭ fe-k′ : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i)))
  (@♭ fe-ij′ : FunExt₂ i (lsuc i))
  (@♭ fe-jk′ : FunExt₂ (lsuc i) (lsuc (lsuc i)))
  (@♭ pe-i′ : PropExt i)
  (@♭ pe-j′ : PropExt (lsuc i))
  (@♭ Qj′ : Quotients (lsuc i))
  (@♭ Ej′ : Eliminates Qj′ (lsuc i))
  (@♭ effective-j′ : Effective Qj′)
  (@♭ Qk′ : Quotients (lsuc (lsuc i)))
  (@♭ Ek′ : Eliminates Qk′ (lsuc (lsuc i)))
  (@♭ b-j b-j′ : FunExtAt (lsuc i))
  (@♭ b-k b-k′ : FunExtAt (lsuc (lsuc i)))
  (@♭ B B′ : Set i) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ B-set : IsSet B) (@♭ B′-set : IsSet B′) (@♭ f : B′ → B)
  -- the payload part, twice
  (@♭ A : B → Set i) (@♭ A-set : (b : B) → IsSet (A b))
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f))
  (@♭ A° : B → Set i) (@♭ A°-set : (b : B) → IsSet (A° b))
  (@♭ K° : RelativeShapeOver B dB A°)
  (@♭ K°′ : RelativeShapeOver B′ dB′ (A° ∘ f))
  (@♭ KO : Closed (♯ (O i)))
  where

  module M = Statements.Kernel
    fe-i fe-j fe-k fe-ij fe-jk pe-i pe-j Qj Ej effective-j Qk Ek
    B B′ dB dB′ B-set B′-set A A-set f K K′
    (Bridge.data-of b-j (♯ (O i)) KO)
  module N = Statements.Kernel
    fe-i′ fe-j′ fe-k′ fe-ij′ fe-jk′ pe-i′ pe-j′ Qj′ Ej′ effective-j′ Qk′ Ek′
    B B′ dB dB′ B-set B′-set A° A°-set f K° K°′
    (Bridge.data-of b-j′ (♯ (O i)) KO)

  Q-same : M.Pr.Q ≡ N.Pr.Q
  Q-same = refl

  R-same : M.Pr.R ≡ N.Pr.R
  R-same = refl

  F-same : M.Pr.F ≡ N.Pr.F
  F-same = refl

  module Support
    (@♭ KQ : Closed M.Pr.Q) (@♭ KR : Closed M.Pr.R)
    (@♭ KE : Closed (M.Pr.F → ♯ (O i)))
    (@♭ KYQ : Closed (♯ M.Pr.Q))
    (@♭ upQ : ClosedLargeUP (lsuc (lsuc i)) (♯ M.Pr.Q) KYQ)
    (@♭ KOj : Closed (♯ (O (lsuc i))))
    where

    module M2 = M.Support
      (Bridge.data-of b-j M.Pr.Q KQ) (Bridge.data-of b-k M.Pr.R KR)
      (Bridge.data-of b-j (M.Pr.F → ♯ (O i)) KE)
      (Bridge.data-of b-j (♯ M.Pr.Q) KYQ)
      (attach (lsuc (lsuc i)) (♯ M.Pr.Q) KYQ upQ b-j)
      (Bridge.data-of b-k (♯ (O (lsuc i))) KOj)
    module N2 = N.Support
      (Bridge.data-of b-j′ N.Pr.Q KQ) (Bridge.data-of b-k′ N.Pr.R KR)
      (Bridge.data-of b-j′ (N.Pr.F → ♯ (O i)) KE)
      (Bridge.data-of b-j′ (♯ N.Pr.Q) KYQ)
      (attach (lsuc (lsuc i)) (♯ N.Pr.Q) KYQ upQ b-j′)
      (Bridge.data-of b-k′ (♯ (O (lsuc i))) KOj)

    P-same : M2.P ≡ N2.P
    P-same = refl

    C-same : M2.C ≡ N2.C
    C-same = refl

------------------------------------------------------------------------
-- 4. The same, for the attachment. Varied: the three parameters of
--    section 2, the bridging extensionality at k (in the shapes of R and
--    of ♯ (O j)) and the payload part. Shared: the nine, and the bridging
--    extensionality at j.

module BridgesNotThree {@♭ i : Level}
  (@♭ fe-i : FunExt₂ i i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  (@♭ fe-k : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i)))
  (@♭ fe-ij : FunExt₂ i (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i)))
  (@♭ pe-i : PropExt i)
  (@♭ pe-j : PropExt (lsuc i))
  (@♭ Qj : Quotients (lsuc i))
  (@♭ Ej : Eliminates Qj (lsuc i))
  (@♭ effective-j : Effective Qj)
  (@♭ Qk : Quotients (lsuc (lsuc i)))
  (@♭ Ek : Eliminates Qk (lsuc (lsuc i)))
  (@♭ fe-k′ : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i)))
  (@♭ fe-ij′ : FunExt₂ i (lsuc i))
  (@♭ effective-j′ : Effective Qj)
  (@♭ b-j : FunExtAt (lsuc i))
  (@♭ b-k b-k′ : FunExtAt (lsuc (lsuc i)))
  (@♭ B B′ : Set i) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ B-set : IsSet B) (@♭ B′-set : IsSet B′) (@♭ f : B′ → B)
  -- the payload part, twice
  (@♭ A : B → Set i) (@♭ A-set : (b : B) → IsSet (A b))
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f))
  (@♭ A° : B → Set i) (@♭ A°-set : (b : B) → IsSet (A° b))
  (@♭ K° : RelativeShapeOver B dB A°)
  (@♭ K°′ : RelativeShapeOver B′ dB′ (A° ∘ f))
  (@♭ KO : Closed (♯ (O i)))
  where

  module M = Statements.Kernel
    fe-i fe-j fe-k fe-ij fe-jk pe-i pe-j Qj Ej effective-j Qk Ek
    B B′ dB dB′ B-set B′-set A A-set f K K′
    (Bridge.data-of b-j (♯ (O i)) KO)
  module N = Statements.Kernel
    fe-i fe-j fe-k′ fe-ij′ fe-jk pe-i pe-j Qj Ej effective-j′ Qk Ek
    B B′ dB dB′ B-set B′-set A° A°-set f K° K°′
    (Bridge.data-of b-j (♯ (O i)) KO)

  Q-same : M.Pr.Q ≡ N.Pr.Q
  Q-same = refl

  R-same : M.Pr.R ≡ N.Pr.R
  R-same = refl

  F-same : M.Pr.F ≡ N.Pr.F
  F-same = refl

  module Support
    (@♭ KQ : Closed M.Pr.Q) (@♭ KR : Closed M.Pr.R)
    (@♭ KE : Closed (M.Pr.F → ♯ (O i)))
    (@♭ KYQ : Closed (♯ M.Pr.Q))
    (@♭ upQ : ClosedLargeUP (lsuc (lsuc i)) (♯ M.Pr.Q) KYQ)
    (@♭ KOj : Closed (♯ (O (lsuc i))))
    where

    module M2 = M.Support
      (Bridge.data-of b-j M.Pr.Q KQ) (Bridge.data-of b-k M.Pr.R KR)
      (Bridge.data-of b-j (M.Pr.F → ♯ (O i)) KE)
      (Bridge.data-of b-j (♯ M.Pr.Q) KYQ)
      (attach (lsuc (lsuc i)) (♯ M.Pr.Q) KYQ upQ b-j)
      (Bridge.data-of b-k (♯ (O (lsuc i))) KOj)
    module N2 = N.Support
      (Bridge.data-of b-j N.Pr.Q KQ) (Bridge.data-of b-k′ N.Pr.R KR)
      (Bridge.data-of b-j (N.Pr.F → ♯ (O i)) KE)
      (Bridge.data-of b-j (♯ N.Pr.Q) KYQ)
      (attach (lsuc (lsuc i)) (♯ N.Pr.Q) KYQ upQ b-j)
      (Bridge.data-of b-k′ (♯ (O (lsuc i))) KOj)

    false-endpoint-same : M2.bottom ≡ N2.bottom
    false-endpoint-same = refl

    closed-base-same : (@♭ V : Set i) → M2.Att.G V ≡ N2.Att.G V
    closed-base-same V = refl

    attachment-same : (@♭ V : Set i) → M2.Att.U V ≡ N2.Att.U V
    attachment-same V = refl

------------------------------------------------------------------------
-- 5. Carrier and unit of the shape datum made from a closed relative
--    shape do not depend on the extensionality used for its other fields.

module BridgeCarrier {@♭ ℓ : Level} (@♭ fe fe′ : FunExtAt ℓ)
  (@♭ X : Set ℓ) (@♭ K : Closed X) where

  carrier-same : ʃ (Bridge.data-of fe X K) ≡ ʃ (Bridge.data-of fe′ X K)
  carrier-same = refl

  unit-same : η (Bridge.data-of fe X K) ≡ η (Bridge.data-of fe′ X K)
  unit-same = refl
