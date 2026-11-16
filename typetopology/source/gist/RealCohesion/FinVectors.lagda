Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Functions on Fin n as vectors: a vector with a new first entry, and a
vector of length n + 1 as its first entry followed by the rest; the
vector of length 2 with two given entries (Fin-pair, added for
gist.RealCohesion.RealMultiplication, gate G14); and choice over Fin n
for propositional truncations (Fin-choice, added for
gist.RealCohesion.CrispUniformContinuityOnBoxes and
gist.RealCohesion.CrispExtensionOnBoxes, gate G21).

These were in gist.RealCohesion.CrispRationals, which still exports
them. They are here so that modules without --cohesion can use them:
Agda does not let a module without --cohesion import one with it. The
rational detection in n variables of gist.RealCohesion.RationalDetection
uses them.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.FinVectors where

open import MLTT.Spartan
open import Fin.Type
open import UF.FunExt
open import UF.PropTrunc

Fin-cons : {𝓤 : Universe} {A : 𝓤 ̇ } {m : ℕ} → A → (Fin m → A) → Fin (succ m)
         → A
Fin-cons a f 𝟎       = a
Fin-cons a f (suc i) = f i

Fin-cons-of-parts : {𝓤 : Universe} {A : 𝓤 ̇ } → funext 𝓤₀ 𝓤
                  → {m : ℕ} (f : Fin (succ m) → A)
                  → Fin-cons (f 𝟎) (f ∘ suc) ＝ f
Fin-cons-of-parts fe f = dfunext fe γ
 where
  γ : Fin-cons (f 𝟎) (f ∘ suc) ∼ f
  γ 𝟎       = refl
  γ (suc i) = refl

Fin-pair : {𝓤 : Universe} {A : 𝓤 ̇ } → A → A → Fin 2 → A
Fin-pair a b 𝟎             = a
Fin-pair a b 𝟏             = b
Fin-pair a b (suc (suc i)) = 𝟘-elim i

\end{code}

If each A i is inhabited, so is the type of their choices: by
induction on n, with binary choice.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 Fin-choice : {𝓤 : Universe} (n : ℕ) {A : Fin n → 𝓤 ̇ }
            → ((i : Fin n) → ∥ A i ∥) → ∥ ((i : Fin n) → A i) ∥
 Fin-choice 0        f = ∣ (λ ()) ∣
 Fin-choice (succ n) {A} f =
  ∥∥-functor γ (binary-choice (f 𝟎) (Fin-choice n (λ i → f (suc i))))
  where
   γ : A 𝟎 × ((i : Fin n) → A (suc i)) → (i : Fin (succ n)) → A i
   γ (x , g) 𝟎       = x
   γ (x , g) (suc i) = g i

\end{code}
