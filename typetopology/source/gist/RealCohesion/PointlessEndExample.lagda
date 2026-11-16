Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

A small instance of gist.RealCohesion.PointlessEnd.

The results of gist.RealCohesion.PointlessEnd are relative to
hypotheses on the frames O, B and L, on the filter C, on the frame
homomorphism g and on the completely prime filter p. Here we
instantiate all of them at once, constructively: O and L are the
frame Ω of truth values, which is the frame of the one-point locale,
C and p are the filter of true propositions, g is the identity, and B
is the Cohen frame of gist.RealCohesion.CohenFrame.

The result is a locale with one point, whose closure contains a
pointless locale. It is not the locale X of [1, §2], where O is the
frame of the open interval (0,1). The point of the example is only
that the hypotheses are consistent, so that the results are not
vacuous. The statement about points also assumes excluded middle, as
in gist.RealCohesion.PointlessEnd.

Like several modules of TypeTopology's locale library, this module
uses --lossy-unification. Without it, Agda takes a long time to
compare the statements below with the instantiated statements of
gist.RealCohesion.PointlessEnd.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import MLTT.List hiding ([_])
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.PointlessEndExample
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.Frame pt fe hiding (𝟚 ; ₀ ; ₁)
open import Locales.InitialFrame pt fe
open import Locales.Point.Definition pt fe
open import Slice.Family
open import UF.ClassicalLogic
open import UF.Logic
open import UF.SubtypeClassifier
open import gist.RealCohesion.CohenFrame pt fe pe
open import gist.RealCohesion.Cylinders pt fe
open import gist.RealCohesion.PointlessEnd pt fe pe

open AllCombinators pt fe hiding (_∨_)
open DefnOfCPF
open FrameHomomorphisms
open PropositionalTruncation pt

\end{code}

The frame of truth values and its filter of true propositions.

\begin{code}

Ω-frame : Frame 𝓤₁ 𝓤₀ 𝓤₀
Ω-frame = 𝟎-𝔽𝕣𝕞 pe

T : Ω 𝓤₀ → Ω 𝓤₀
T V = V

T-is-upward-closed : (V W : Ω 𝓤₀) → (V ≤[ poset-of Ω-frame ] W) holds
                   → T V holds → T W holds
T-is-upward-closed V W l h = l h

T-contains-𝟏 : T 𝟏[ Ω-frame ] holds
T-contains-𝟏 = ⋆

T-is-closed-under-∧ : (V W : Ω 𝓤₀) → T V holds → T W holds
                    → T (V ∧[ Ω-frame ] W) holds
T-is-closed-under-∧ V W h k = h , k

T-is-proper : ¬ (T 𝟎[ Ω-frame ] holds)
T-is-proper h = ∥∥-rec 𝟘-is-prop (λ (i , _) → 𝟘-elim i) h

T-is-completely-prime : (S : Fam 𝓤₀ (Ω 𝓤₀))
                      → T (⋁[ Ω-frame ] S) holds
                      → ∃ i ꞉ index S , T (S [ i ]) holds
T-is-completely-prime S h = h

\end{code}

The instance.

\begin{code}

open glued-frame Ω-frame Cohen-frame T
      T-is-upward-closed T-contains-𝟏 T-is-closed-under-∧

open glued-points Ω-frame Cohen-frame T
      T-is-upward-closed T-contains-𝟏 T-is-closed-under-∧
 using (X ; collar-contains-every-point-but-is-not-𝟏)

example-points : EM 𝓤₀
               → ((x : Point X) → pr₁ x collar holds) × (collar ≠ 𝟏[ Gl ])
example-points em = collar-contains-every-point-but-is-not-𝟏 em Cohen-cylinders
                     Cohen-frame-is-nontrivial

example-density : (x : Glued) → x ∧[ Gl ] collar ＝ 𝟎[ Gl ] → x ＝ 𝟎[ Gl ]
example-density = collar-is-dense T-is-proper

open fan Cohen-cylinders

example-fan : (W : Fam 𝓤₀ Glued)
            → ⋁[ Gl ] W ＝ 𝟏[ Gl ]
            → ((j : index W) → ∃ N ꞉ ℕ , ((u : List 𝟚) → length u ＝ N
                → ((W [ j ]) ≤ᴳ (⋁[ Gl ] ⁅ bar t ∣ t ε initial-segments u ⁆))
                   holds))
            → 𝟘
example-fan = no-uniformly-barred-cover Cohen-frame-is-nontrivial

id-is-frame-homomorphism : is-a-frame-homomorphism Ω-frame Ω-frame id holds
id-is-frame-homomorphism =
 refl , (λ _ _ → refl) , (λ S → ⋁[ Ω-frame ]-upper S , ⋁[ Ω-frame ]-least S)

open coordinate Ω-frame id id-is-frame-homomorphism T
      T-is-upward-closed T-contains-𝟏 T-is-closed-under-∧
      T-is-completely-prime (λ W h → h)

example-coordinate : is-a-frame-homomorphism Ω-frame Gl t* holds
example-coordinate = t*-is-frame-homomorphism

\end{code}
