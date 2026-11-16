Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026; prose corrected 13 November 2026, after
the final audits. See the AI disclosure in gist.RealCohesion.index.

The exact intermediate value theorem for crisp functions, without
Axiom T, for crisp witnesses.

Shulman's Theorem 11.2 [1]: if f : ℝ → ℝ and c : ℝ are crisp and
f a < c < f b for some a and b, then f x ＝ c for some x. No
continuity hypothesis is needed, because crisp functions are
continuous. Shulman assumes crisp excluded middle and Axioms R♭ and T.
Fable's note [2, Theorem A.3] removes Axiom T, and we formalize the
result for crisp a and b, from crisp excluded middle and the constancy
of maps ℝ → Q, which follows from Axiom R♭.

For arbitrary a and b, Shulman first makes them crisp: the hypothesis
is a crisp proposition, and ♭ commutes with propositional truncation
[1, Corollary 6.7]. That step needs crisp induction on the truncation,
which was not available for TypeTopology's truncations when this
module was written (see gist.RealCohesion.CrispContinuity), so this
module treats crisp a and b. Arbitrary a and b are reached later by
rational detection, in gist.RealCohesion.CrispFunctionsEverywhere.

The proof uses the connectedness of rational intervals at crisp
points (gist.RealCohesion.CrispConnectedness), not a new bisection.
By crisp excluded middle it is enough to refute the absence of a
root. Rational detection (gist.RealCohesion.RationalDetection) moves a
and b to crisp rationals α and β, with f α < c < f β. If f has no root, then at
every crisp point either f < c or c < f, by crisp excluded middle and the
tightness of the order. So the crisp predicate f < c and its negation are open
at crisp points, and connectedness says that it holds at α if and only if at β,
which is false.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] Fable. Shulman's stated questions: three updates, Part A.
    Working note, 10 November 2026, audited by GPT-6 Astra.
    references/F18-shulman-three-updates.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispExactIVT
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt using (ℝ<-tight) public
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.CrispDecisions using (Crisp-EM-lower)
open import gist.RealCohesion.CrispRationals
 using (ℚ-has-crisp-representatives ; crisp-witness)
open import gist.RealCohesion.CrispRealAnalysis fe pe pt
 using (Holds-Near ; holds-near-map)
open import gist.RealCohesion.RationalDetection fe pe pt
 using (rational-detection-window)
open import gist.RealCohesion.CrispConnectedness fe pe pt
 using (crisp-interval-is-connected)
open import gist.RealCohesion.CrispContinuity fe pe pt
 using (crisp-real-continuity)

open PropositionalTruncation pt

\end{code}

The strict order of reals is asymmetric and tight.

\begin{code}

ℝ<-asymmetric : (x y : ℝ) → x < y → y < x → 𝟘 {𝓤₀}
ℝ<-asymmetric x y l m = <ℝ-irreflexive x (ℝ<-trans x y x l m)


\end{code}

The crisp family of points where f is below c.

\begin{code}

Below : (ℝ → ℝ) → ℝ → ℝ → 𝓤₀ ̇
Below f c s = f s < c

Below-is-prop : (f : ℝ → ℝ) (c s : ℝ) → is-prop (Below f c s)
Below-is-prop f c s = <-is-prop (f s) c

\end{code}

We assume crisp excluded middle and that maps ℝ → Q are constant.

\begin{code}

module _ (@♭ cem : Crisp-EM 𝓤₁) where

 cem₀ : Crisp-EM 𝓤₀
 cem₀ = Crisp-EM-lower {𝓤₀} {𝓤₁} cem

 module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

  below-is-open : (@♭ f : ℝ → ℝ) (@♭ c t : ℝ)
                → f t < c → Holds-Near (λ s → f s < c) t
  below-is-open f c t l = ∥∥-rec ∃-is-prop γ l
   where
    γ : (Σ w ꞉ ℚ , (f t < w) × (w < c)) → Holds-Near (λ s → f s < c) t
    γ (w , o , o') = ∥∥-rec ∃-is-prop δ (inhabited-from-real-L (f t))
     where
      narrow : (@♭ s : ℝ) → (Σ L ꞉ ℚ , (L < f s) × (f s < w)) → f s < c
      narrow s (_ , _ , k) = ∣ w , k , o' ∣

      δ : (Σ L ꞉ ℚ , L < f t) → Holds-Near (λ s → f s < c) t
      δ (L , p) = holds-near-map (λ s → (L < f s) × (f s < w)) (λ s → f s < c) t
                   (λ s k → narrow s (L , k))
                   (crisp-real-continuity cem ν f t L w p o)

  above-is-open : (@♭ f : ℝ → ℝ) (@♭ c t : ℝ)
                → c < f t → Holds-Near (λ s → c < f s) t
  above-is-open f c t l = ∥∥-rec ∃-is-prop γ l
   where
    γ : (Σ w ꞉ ℚ , (c < w) × (w < f t)) → Holds-Near (λ s → c < f s) t
    γ (w , o , o') = ∥∥-rec ∃-is-prop δ (inhabited-from-real-R (f t))
     where
      narrow : (@♭ s : ℝ) → (Σ U ꞉ ℚ , (w < f s) × (f s < U)) → c < f s
      narrow s (_ , k , _) = ∣ w , o , k ∣

      δ : (Σ U ꞉ ℚ , f t < U) → Holds-Near (λ s → c < f s) t
      δ (U , p) = holds-near-map (λ s → (w < f s) × (f s < U)) (λ s → c < f s) t
                   (λ s k → narrow s (U , k))
                   (crisp-real-continuity cem ν f t w U o' p)

\end{code}

Crisp rational witnesses, at arbitrary points: if f a < c, rational
detection gives a rational q with f q < c, and rationals are crisp.
Likewise above.

\begin{code}

  rational-below : (@♭ f : ℝ → ℝ) (@♭ c : ℝ) (a : ℝ)
                 → f a < c → ∃ α ꞉ ♭ ℚ , f (ι (♭-counit α)) < c
  rational-below f c a l = ∥∥-rec ∃-is-prop γ l
   where
    γ : (Σ w ꞉ ℚ , (f a < w) × (w < c)) → ∃ α ꞉ ♭ ℚ , f (ι (♭-counit α)) < c
    γ (w , o , o') = ∥∥-rec ∃-is-prop δ (inhabited-from-real-L (f a))
     where
      δ : (Σ L ꞉ ℚ , L < f a) → ∃ α ꞉ ♭ ℚ , f (ι (♭-counit α)) < c
      δ (L , L<fa) = ∥∥-functor ε (rational-detection-window ν f a L w L<fa o)
       where
        ε : (Σ q ꞉ ℚ , (L < f (ιₐ q)) × (f (ιₐ q) < w))
          → Σ α ꞉ ♭ ℚ , f (ι (♭-counit α)) < c
        ε (q , _ , k) =
         crisp-witness ℚ-has-crisp-representatives (λ q → f (ι q) < c) q
                         ∣ w , transport (λ - → f - < w) (ιₐ-is-ι q) k , o' ∣

  rational-above : (@♭ f : ℝ → ℝ) (@♭ c : ℝ) (b : ℝ)
                 → c < f b → ∃ β ꞉ ♭ ℚ , c < f (ι (♭-counit β))
  rational-above f c b l = ∥∥-rec ∃-is-prop γ l
   where
    γ : (Σ w ꞉ ℚ , (c < w) × (w < f b)) → ∃ β ꞉ ♭ ℚ , c < f (ι (♭-counit β))
    γ (w , o , o') = ∥∥-rec ∃-is-prop δ (inhabited-from-real-R (f b))
     where
      δ : (Σ U ꞉ ℚ , f b < U) → ∃ β ꞉ ♭ ℚ , c < f (ι (♭-counit β))
      δ (U , fb<U) = ∥∥-functor ε (rational-detection-window ν f b w U o' fb<U)
       where
        ε : (Σ q ꞉ ℚ , (w < f (ιₐ q)) × (f (ιₐ q) < U))
          → Σ β ꞉ ♭ ℚ , c < f (ι (♭-counit β))
        ε (q , k , _) =
         crisp-witness ℚ-has-crisp-representatives (λ q → c < f (ι q)) q
                         ∣ w , o , transport (λ - → w < f -) (ιₐ-is-ι q) k ∣

\end{code}

Without a root, f < c and its negation are open at crisp points.

\begin{code}

  module _ (@♭ f : ℝ → ℝ) (@♭ c : ℝ) (no-root : ¬ (∃ x ꞉ ℝ , f x ＝ c)) where

   not-below-is-open : (@♭ t : ℝ) → ¬ (f t < c)
                     → Holds-Near (λ s → ¬ (f s < c)) t
   not-below-is-open t n = holds-near-map (λ s → c < f s) (λ s → ¬ (f s < c)) t
                            (λ s k → ℝ<-asymmetric c (f s) k)
                            (above-is-open f c t above)
    where
     above : c < f t
     above = Cases (cem₀ (c < f t) (<-is-prop c (f t))) id
              (λ n' → 𝟘-elim (no-root ∣ t , ℝ<-tight (f t) c n n' ∣))

   ends-agree : (@♭ α β : ℚ) → α < β → (f (ι α) < c) ↔ (f (ι β) < c)
   ends-agree α β α<β =
    crisp-interval-is-connected cem₀ (Below f c) (Below-is-prop f c)
                         α β α<β
                         (λ t _ _ l → below-is-open f c t l)
                         (λ t _ _ n → not-below-is-open t n)

   no-root-is-impossible : (@♭ a b : ℝ) → f a < c → c < f b → 𝟘 {𝓤₀}
   no-root-is-impossible a b l m = ∥∥-rec 𝟘-is-prop γ (rational-below f c a l)
    where
     γ : (Σ α ꞉ ♭ ℚ , f (ι (♭-counit α)) < c) → 𝟘
     γ ((α ^♭) , l') = ∥∥-rec 𝟘-is-prop δ (rational-above f c b m)
      where
       δ : (Σ β ꞉ ♭ ℚ , c < f (ι (♭-counit β))) → 𝟘
       δ ((β ^♭) , m') = ε (ℚ-trichotomous α β)
        where
         ε : (α < β) ∔ (α ＝ β) ∔ (β < α) → 𝟘
         ε (inl α<β)       = ℝ<-asymmetric (f (ι β)) c
                              (lr-implication (ends-agree α β α<β) l') m'
         ε (inr (inl e))   = ℝ<-asymmetric (f (ι α)) c l'
                              (transport (λ - → c < f (ι -)) (e ⁻¹) m')
         ε (inr (inr β<α)) = ℝ<-asymmetric (f (ι β)) c
                              (rl-implication (ends-agree β α β<α) l') m'

\end{code}

The theorem.

\begin{code}

  crisp-exact-IVT : (@♭ f : ℝ → ℝ) (@♭ c a b : ℝ)
                  → f a < c → c < f b
                  → ∃ x ꞉ ℝ , f x ＝ c
  crisp-exact-IVT f c a b l m =
   Cases (cem (∃ x ꞉ ℝ , f x ＝ c) ∃-is-prop) id
    (λ n → 𝟘-elim (no-root-is-impossible f c n a b l m))

\end{code}
