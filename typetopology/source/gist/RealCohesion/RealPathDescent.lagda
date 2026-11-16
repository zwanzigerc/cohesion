Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index. Following a gameplan by GPT-6 Astra
(25 October 2026) [3].

Unique real-path descent for Boolean functions.

For a crisp set X, a function h : ♭ X → 𝟚 on the crisp points of X
is invariant along real paths if h takes the same value at the two
endpoints of every crisp real path γ : ℝ → X. The principle below says
that such an h extends uniquely to a function X → 𝟚, in the sense that
the type of crisp extensions is contractible:

  is-singleton (♭ (Σ f ꞉ (X → 𝟚) , ((u : ♭ X) → f (♭-counit u) ＝ h u))).

Both halves matter. Existence gives a function on all of X from its
values at crisp points. Uniqueness is what lets us prove equations
between such functions at arbitrary, not only crisp, points: two crisp
extensions of the same h are equal.

The principle is an assumption, not a consequence of Shulman's axioms
that we know of. It holds in Shulman's intended model, sheaves on
Cartesian spaces with continuous maps [1, §7], also with crisp
parameters: for a plot u : ℝⁿ → X, any two points of ℝⁿ are joined by
an affine real path, so h is constant on the points of the plot, and
assigning this constant to the plot gives the unique map of sheaves.
It is the Boolean instance of a connectedness principle for real
paths; the detection of continuity by Cartesian powers of Myers and
Riley [2] is a stronger principle of the same kind.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] David Jaz Myers and Mitchell Riley. Commuting cohesions.
    https://arxiv.org/abs/2301.13780

[3] GPT-6 Astra. Gameplan for Opus: a subset of the Dedekind reals
    whose shape is not a set, 25 October 2026.
    references/A32-subset-shape-gameplan.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RealPathDescent
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import UF.Base
open import UF.Sets
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Flat

\end{code}

The two notions, and the principle.

\begin{code}

Real-Path-Invariant : {@♭ 𝓤 : Universe} (@♭ X : 𝓤 ̇ ) → (♭ X → 𝟚) → 𝓤 ⊔ 𝓤₁ ̇
Real-Path-Invariant X h = (@♭ γ : ℝ → X) → h ((γ 0ℝ) ^♭) ＝ h ((γ 1ℝ) ^♭)

Boolean-Extension : {@♭ 𝓤 : Universe} (@♭ X : 𝓤 ̇ ) → (♭ X → 𝟚) → 𝓤 ̇
Boolean-Extension X h = Σ f ꞉ (X → 𝟚) , ((u : ♭ X) → f (♭-counit u) ＝ h u)

Unique-Boolean-Real-Path-Descent : (@♭ 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓤₁ ̇
Unique-Boolean-Real-Path-Descent 𝓤 =
   (@♭ X : 𝓤 ̇ )
 → @♭ is-set X
 → (@♭ h : ♭ X → 𝟚)
 → @♭ Real-Path-Invariant X h
 → is-singleton (♭ (Boolean-Extension X h))

\end{code}

Two crisp extensions of the same function are equal, at every point.

\begin{code}

module _ {@♭ 𝓤 : Universe}
         (descent : Unique-Boolean-Real-Path-Descent 𝓤)
         {@♭ X : 𝓤 ̇ }
         (@♭ X-is-set : is-set X)
         {@♭ h : ♭ X → 𝟚}
         (@♭ h-is-invariant : Real-Path-Invariant X h)
       where

 crisp-extensions-agree : (@♭ e e' : Boolean-Extension X h)
                        → (x : X) → pr₁ e x ＝ pr₁ e' x
 crisp-extensions-agree e e' x = happly (ap pr₁ I) x
  where
   I : e ＝ e'
   I = ap ♭-counit
        (singletons-are-props (descent X X-is-set h h-is-invariant)
          (e ^♭) (e' ^♭))

\end{code}

To use the extension, we eliminate the center of contraction. Its
components are crisp, so the extension is given to a continuation that
takes them as crisp arguments.

\begin{code}

 with-crisp-extension : {𝓦 : Universe} {C : 𝓦 ̇ }
                      → ((@♭ e : Boolean-Extension X h) → C)
                      → C
 with-crisp-extension {𝓦} {C} k =
  γ (center (descent X X-is-set h h-is-invariant))
  where
   γ : ♭ (Boolean-Extension X h) → C
   γ (e ^♭) = k e

\end{code}
