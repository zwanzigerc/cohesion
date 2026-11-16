Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.CohesiveApartness.index.

This module is licensed under the GNU General Public License, version 3.
SPDX-License-Identifier: GPL-3.0-only

Consequences of crisp induction, from the native ♯, in --safe mode.

We derive four consequences of Shulman's crisp induction principles
[1, §5]:

 * the constructor of ♭ respects crisp identifications, the decoding
   half of Shulman's characterization of the identity types of ♭ A
   [1, Theorem 6.1];

 * 𝟚 is ♭-discrete [1, Theorems 6.19 and 6.21];

 * ℕ is ♭-discrete;

 * ♭ A is ♭-discrete for every crisp type A [1, §6.2].

This folder uses the second: that 𝟚 is ♭-discrete. The other three
follow by the same method and are recorded for use elsewhere.

Agda 2.8 has no ♯, so these facts have to be proved there by pattern
matching on crisp variables, with --flat-split, which Agda does not
allow together with --safe and --without-K; that is how
gist.CohesiveApartness.FlatSplit proves the ♭-discreteness of 𝟚.
Shulman proves crisp induction from ♯ instead [1, §5], and with the
native ♯ of Agda 2.9.0 (gist.CohesiveApartness.Sharp) his method
works in --safe mode.

The method, for crisp-ap-^♭: if x, y and p : x ＝ y are crisp, the
family z ↦ ♯ (x ^♭ ＝ z ^♭) is well formed, because in a type ♯ B
every variable counts as crisp. Transporting the unit of refl along p
gives an element of ♯ (x ^♭ ＝ y ^♭) that is a crisp term, and
eliminating ♯ from it gives x ^♭ ＝ y ^♭.

For 𝟚, ℕ and ♭ A, let s be the section of the counit defined by
ordinary induction, and s' the map to ♯ (♭ A) that sends a to a ^♭,
which is defined by copattern matching because a counts as crisp
there. Ordinary induction shows that the unit of ♯ agrees with s'
after s. For crisp a, transporting along this identification in the
family w ↦ ♯ (s a ＝ w .ε♯) and eliminating ♯ gives s a ＝ a ^♭.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.CohesiveApartness.CrispInduction where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import gist.CohesiveApartness.Flat
open import gist.CohesiveApartness.Sharp

\end{code}

The constructor of ♭ respects crisp identifications.

\begin{code}

crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
            → @♭ x ＝ y → x ^♭ ＝ y ^♭
crisp-ap-^♭ {𝓤} {A} {x} {y} p =
 crisp-elim-sharp (transport (λ z → ♯ (x ^♭ ＝ z ^♭)) p (unit-sharp refl))

\end{code}

𝟚 is ♭-discrete.

\begin{code}

𝟚-is-♭-discrete : is-♭-discrete 𝟚
𝟚-is-♭-discrete = qinvs-are-equivs ♭-counit (s , retraction , section)
 where
  s : 𝟚 → ♭ 𝟚
  s ₀ = ₀ ^♭
  s ₁ = ₁ ^♭

  s' : 𝟚 → ♯ (♭ 𝟚)
  s' b .ε♯ = b ^♭

  agreement : (b : 𝟚) → unit-sharp (s b) ＝ s' b
  agreement ₀ = refl
  agreement ₁ = refl

  crisp-retraction : (@♭ b : 𝟚) → s b ＝ b ^♭
  crisp-retraction b =
   crisp-elim-sharp
    (transport (λ w → ♯ (s b ＝ w .ε♯)) (agreement b) (unit-sharp refl))

  retraction : s ∘ ♭-counit ∼ id
  retraction (b ^♭) = crisp-retraction b

  section : ♭-counit ∘ s ∼ id
  section ₀ = refl
  section ₁ = refl

\end{code}

ℕ is ♭-discrete.

\begin{code}

♭-succ : ♭ ℕ → ♭ ℕ
♭-succ (n ^♭) = succ n ^♭

ℕ-to-♭ℕ : ℕ → ♭ ℕ
ℕ-to-♭ℕ 0        = 0 ^♭
ℕ-to-♭ℕ (succ n) = ♭-succ (ℕ-to-♭ℕ n)

ℕ-is-♭-discrete : is-♭-discrete ℕ
ℕ-is-♭-discrete = qinvs-are-equivs ♭-counit (ℕ-to-♭ℕ , retraction , section)
 where
  s' : ℕ → ♯ (♭ ℕ)
  s' n .ε♯ = n ^♭

  agreement : (n : ℕ) → unit-sharp (ℕ-to-♭ℕ n) ＝ s' n
  agreement 0        = refl
  agreement (succ n) = ap (♯-map ♭-succ) (agreement n)

  crisp-retraction : (@♭ n : ℕ) → ℕ-to-♭ℕ n ＝ n ^♭
  crisp-retraction n =
   crisp-elim-sharp
    (transport (λ w → ♯ (ℕ-to-♭ℕ n ＝ w .ε♯)) (agreement n) (unit-sharp refl))

  retraction : ℕ-to-♭ℕ ∘ ♭-counit ∼ id
  retraction (n ^♭) = crisp-retraction n

  section : ♭-counit ∘ ℕ-to-♭ℕ ∼ id
  section 0        = refl
  section (succ n) = γ (ℕ-to-♭ℕ n) (section n)
   where
    γ : (x : ♭ ℕ) → ♭-counit x ＝ n → ♭-counit (♭-succ x) ＝ succ n
    γ (m ^♭) e = ap succ e

\end{code}

♭ A is ♭-discrete.

\begin{code}

♭-is-♭-discrete : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } → is-♭-discrete (♭ A)
♭-is-♭-discrete {𝓤} {A} = qinvs-are-equivs ♭-counit (σ , retraction , section)
 where
  σ : ♭ A → ♭ (♭ A)
  σ (a ^♭) = (a ^♭) ^♭

  σ' : ♭ A → ♯ (♭ (♭ A))
  σ' v .ε♯ = v ^♭

  agreement : (v : ♭ A) → unit-sharp (σ v) ＝ σ' v
  agreement (a ^♭) = refl

  crisp-retraction : (@♭ v : ♭ A) → σ v ＝ v ^♭
  crisp-retraction v =
   crisp-elim-sharp
    (transport (λ w → ♯ (σ v ＝ w .ε♯)) (agreement v) (unit-sharp refl))

  retraction : σ ∘ ♭-counit ∼ id
  retraction (v ^♭) = crisp-retraction v

  section : ♭-counit ∘ σ ∼ id
  section (a ^♭) = refl

\end{code}

The map ℕ → ♭ ℕ and its section proof are adapted from agda-unimath.
The following notice accompanies that code.

MIT License

Copyright (c) 2022 Egbert Maarten Rijke

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
