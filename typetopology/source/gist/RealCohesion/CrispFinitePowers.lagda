Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026, after the final audits. See the AI
disclosure in gist.RealCohesion.index. The code is Claude Fable 5.2's
scratch check FinitePowersCheck.lagda of 13 November 2026 [2,
companion folder, scratch/; SHA-256
ebc6f2113e75f61d8966dd119a8bbd0063a01ccad1e5c7f516bf495e13996ec6],
code of this project and not an external source, adapted only in the
module name and the header.

Crisp representatives of finite powers.

Functions on Fin n with values in a type A with crisp representatives
have crisp representatives, for every crisp n, with no default value
in A:

  finite-powers-have-crisp-representatives
   : Fun-Ext → {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ }
   → has-crisp-representatives A
   → (@♭ n : ℕ) → has-crisp-representatives (Fin n → A)

This is the general statement that gate G9 of the blueprint addendum
asks for [1, Section 5.1]. gist.RealCohesion.CrispRationals has the
form with a crisp default value in A,
Fin-functions-have-crisp-representatives, which its uses keep.

The proof is by induction on the crisp n. Pattern matching on a crisp
natural number needs Agda's --flat-split, which --safe mode does not
allow, so the induction comes from the ♭-discreteness of ℕ, which
gist.CohesiveApartness.CrispInduction derives from the native ♯ of
Agda 2.9.0. The statement for n is a family P over ♭ ℕ, defined by
♭-elimination. Ordinary recursion proves P at ℕ-to-♭ℕ m for every m:
at 0 by the empty function, and at a successor by Fin-cons of the
crisp representatives of the head f 𝟎 and of the tail f ∘ suc. For a
crisp n, ℕ-to-♭ℕ n ＝ n ^♭, because ℕ-to-♭ℕ is the inverse of the
counit, and transport along this identification gives the statement
for n. The map ℕ-to-♭ℕ and the proof that it is a section of the
counit come from the port of agda-unimath's is-flat-discrete-crisp-ℕ,
whose source revision is not recorded (see
gist.CohesiveApartness.CrispInduction).

Function extensionality, the representatives in A and the functions
represented are ordinary; the universe, A and n are crisp. No default
value, choice or new axiom is used. The route is Fable's repair plan
[2, Section 9, R1], after GPT-6 Astra's audit of the plan for gate G9,
and was reviewed by Astra.

This module imports gist.CohesiveApartness.CrispInduction, and so the
native ♯. It is not imported by gist.RealCohesion.CrispRationals,
which is in the import closure of gist.RealCohesion.FlatSplit, the
route that is also checked with Agda 2.8, which has no ♯.

[1] Claude Fable 5.2. Formalization blueprint, addendum: Theorem 7.10,
    Corollary 3.7, Theorem 4.3 and Theorem 8.32, revision 4,
    11 November 2026.
    references/F14-brouwer-addendum-rev4.md

[2] Claude Fable 5.2. Final audit: the Shulman / real-cohesion
    formalization and the Orbifolds targets T1–T5b, 13 November 2026.
    references/F09-final-audit.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.RealCohesion.CrispFinitePowers where

open import MLTT.Spartan
open import Fin.Type
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import gist.CohesiveApartness.Flat
open import gist.CohesiveApartness.CrispInduction
 using (♭-succ ; ℕ-to-♭ℕ ; ℕ-is-♭-discrete)
open import gist.RealCohesion.CrispRationals
 using (has-crisp-representatives ; Fin-cons ; Fin-cons-of-parts)

module _ (fe : Fun-Ext)
         {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ }
         (ρ : has-crisp-representatives A)
       where

 private
  P : ♭ ℕ → 𝓤 ̇
  P (n ^♭) = has-crisp-representatives (Fin n → A)

  base : P (0 ^♭)
  base f = ((λ ()) ^♭) , dfunext fe (λ ())

  step : (x : ♭ ℕ) → P x → P (♭-succ x)
  step (n ^♭) σ f = γ (ρ (f 𝟎)) (σ (f ∘ suc))
   where
    γ : (Σ u ꞉ ♭ A , ♭-counit u ＝ f 𝟎)
      → (Σ v ꞉ ♭ (Fin n → A) , ♭-counit v ＝ f ∘ suc)
      → Σ w ꞉ ♭ (Fin (succ n) → A) , ♭-counit w ＝ f
    γ ((a ^♭) , d) ((g ^♭) , e) =
     (Fin-cons a g ^♭) , (ap₂ Fin-cons d e ∙ Fin-cons-of-parts fe f)

  all-stages : (m : ℕ) → P (ℕ-to-♭ℕ m)
  all-stages 0        = base
  all-stages (succ m) = step (ℕ-to-♭ℕ m) (all-stages m)

 finite-powers-have-crisp-representatives
  : (@♭ n : ℕ) → has-crisp-representatives (Fin n → A)
 finite-powers-have-crisp-representatives n =
  transport P
   (inverses-are-retractions ♭-counit ℕ-is-♭-discrete (n ^♭))
   (all-stages n)

\end{code}
