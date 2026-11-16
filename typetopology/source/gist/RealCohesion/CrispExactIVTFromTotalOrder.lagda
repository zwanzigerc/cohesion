Claude Fable 5.2, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026, as the scratch module
CrispExactIVTSharpCheck (fable-agda-checks-2026-11-12, now
provenance/companions/fable-agda-checks-2026-11-12.zip). Added to the
folder by Claude Opus 5.5 on 12 November 2026, as Fable proposed
(Section 3 of the reply to Astra's audits), with the code unchanged
except the module name, and one sentence of the prose changed: the
target is now stated in gist.RealCohesion.Theorems. See the AI
disclosure in gist.RealCohesion.index.

The exact intermediate value theorem for crisp functions, without
Axiom T, from a hypothesis weaker than crisp excluded middle: that any
two crisp reals x and y come with a choice of x ≤ y or y ≤ x.

Shulman's Theorem 11.2 [1]: if f : ℝ → ℝ and c : ℝ are crisp and
f a < c < f b for some a and b, then f x ＝ c for some x. Shulman
assumes crisp excluded middle and Axioms R♭ and T.
gist.RealCohesion.CrispExactIVT removes Axiom T and assumes crisp
excluded middle for the universe 𝓤₁, which it uses in two places: to
decide whether a root exists, and inside the continuity of crisp
functions (gist.RealCohesion.CrispContinuity). So the target
Target-3-5 of gist.RealCohesion.ShulmanWeakeningsStatements, which
assumes crisp excluded middle for 𝓤₀, was left open. Here neither use
of 𝓤₁ occurs, and gist.RealCohesion.Theorems derives Target-3-5
with its type.

 * The root is constructed, by the bisection of the classical proof.
   A state is an interval [x , x + d] with f x ≤ c and c ≤ f (x + d).
   A step asks, at the midpoint m, for f m ≤ c or c ≤ f m, and keeps
   the half that still brackets c. The limit τ is a crisp real. If
   f τ < c, then f < c at the crisp points of a rational interval
   around τ, which contains a whole stage [x , x + d] of the
   bisection, contradicting c ≤ f (x + d). Likewise c < f τ
   contradicts f x ≤ c. So f τ ＝ c, because the order is tight.

 * The continuity of crisp functions at crisp points is a hypothesis
   here. It follows from Axiom R♭ alone
   (gist.RealCohesion.CrispFunctionsAreContinuous), with no excluded
   middle.

The three hypotheses, each a consequence of the one before:

  Crisp-EM 𝓤₀
  Crisp-Order-Is-Decidable :  x < y or not, for crisp reals x and y
  Crisp-Order-Is-Total     :  a choice of x ≤ y or y ≤ x, for crisp
                              reals x and y

The last is not a proposition: it is a choice function. The theorem
only uses it for x of the form f q with q a crisp rational, and
y ＝ c.

For crisp rationals α and β with f α < c and c < f β we get a root,
not only the existence of a root, and for α < β the inequalities
f α ≤ c ≤ f β suffice.

The first part below is a bisection for two crisp families L and R on
the rationals with a crisp choice of L x or R x at each crisp
rational x. It follows gist.RealCohesion.CrispConnectedness, with one
test for each step instead of two.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispExactIVTFromTotalOrder
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Addition
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import UF.Base
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.NestedIntervals fe pe pt
open import gist.RealCohesion.RationalArithmetic
open import gist.RealCohesion.RationalLimits fe pe pt
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt using (ℝ<-gives-≤)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.CrispRationals
 using (ℚ-has-crisp-representatives ; crisp-witness)
open import gist.RealCohesion.CrispRealAnalysis fe pe pt
 using (Holds-Near ; holds-near-map ; Crisp-Real-Continuity)
open import gist.RealCohesion.RationalDetection fe pe pt
 using (rational-detection-window)
open import gist.RealCohesion.CrispExactIVT fe pe pt
 using (ℝ<-asymmetric ; ℝ<-tight)

open PropositionalTruncation pt

\end{code}

If W holds at the crisp points of the rational interval (r , r'), and
that interval contains the interval of a state of a bisection, then W
holds at both ends of the state. This is a private lemma of
gist.RealCohesion.CrispConnectedness.

\begin{code}

ends-in : {𝓦 : Universe} (W : ℝ → 𝓦 ̇ ) (r r' : ℚ)
        → ((@♭ s : ℝ) → r < s → s < r' → W s)
        → (s : ♭ (ℚ × ℚ))
        → 0ℚ ≤ pr₂ (♭-counit s)
        → r < pr₁ (♭-counit s)
        → pr₁ (♭-counit s) + pr₂ (♭-counit s) < r'
        → W (ιₐ (pr₁ (♭-counit s)))
        × W (ιₐ (pr₁ (♭-counit s) + pr₂ (♭-counit s)))
ends-in W r r' h (p ^♭) l a b =
 h (ιₐ (pr₁ p)) (ιₐ-lower r (pr₁ p) a)
   (ιₐ-upper (pr₁ p) r' (ℚ≤-<-trans (pr₁ p) (pr₁ p + pr₂ p) r' x≤x+d b)) ,
 h (ιₐ (pr₁ p + pr₂ p))
   (ιₐ-lower r (pr₁ p + pr₂ p) (ℚ<-≤-trans r (pr₁ p) (pr₁ p + pr₂ p) a x≤x+d))
   (ιₐ-upper (pr₁ p + pr₂ p) r' b)
 where
  x≤x+d : pr₁ p ≤ pr₁ p + pr₂ p
  x≤x+d = ℚ≤-addition-preserves-order'' (pr₁ p) (pr₂ p) l

\end{code}

The bisection. A state is a crisp pair (x , d), standing for the
interval [x , x + d]. A step asks for L or R at the midpoint. If L
holds there, it keeps the right half, and otherwise the left half.

\begin{code}

module _ {@♭ 𝓦 𝓦' : Universe}
         (@♭ L : ℚ → 𝓦 ̇ )
         (@♭ R : ℚ → 𝓦' ̇ )
         (@♭ choice : (@♭ x : ℚ) → L x ∔ R x)
       where

 side : (x : ℚ) → L x ∔ R x → 𝟚
 side x (inl _) = ₁
 side x (inr _) = ₀

 mid : ℚ × ℚ → ℚ
 mid p = pr₁ p + half (pr₂ p)

 next : 𝟚 → ℚ × ℚ → ℚ × ℚ
 next b p = (halve b (pr₁ p) (pr₂ p) , half (pr₂ p))

 mid-bit : (@♭ p : ℚ × ℚ) → 𝟚
 mid-bit p = side (mid p) (choice (mid p))

 step : ♭ (ℚ × ℚ) → ♭ (ℚ × ℚ)
 step (p ^♭) = (next (mid-bit p) p) ^♭

 bisection : ♭ (ℚ × ℚ) → ℕ → ♭ (ℚ × ℚ)
 bisection s 0        = s
 bisection s (succ n) = step (bisection s n)

 step-halves : (s : ♭ (ℚ × ℚ))
             → pr₂ (♭-counit (step s)) ＝ half (pr₂ (♭-counit s))
 step-halves (p ^♭) = refl

 step-left-grows : (s : ♭ (ℚ × ℚ)) → 0ℚ ≤ pr₂ (♭-counit s)
                 → pr₁ (♭-counit s) ≤ pr₁ (♭-counit (step s))
 step-left-grows (p ^♭) = halve-grows (mid-bit p) (pr₁ p) (pr₂ p)

 step-right-shrinks : (s : ♭ (ℚ × ℚ)) → 0ℚ ≤ pr₂ (♭-counit s)
                    → pr₁ (♭-counit (step s)) + pr₂ (♭-counit (step s))
                      ≤ pr₁ (♭-counit s) + pr₂ (♭-counit s)
 step-right-shrinks (p ^♭) = halve-shrinks (mid-bit p) (pr₁ p) (pr₂ p)

\end{code}

A state is a bracket if L holds at its left end and R at its right
end. A step keeps brackets.

\begin{code}

 Bracket : ℚ × ℚ → 𝓦 ⊔ 𝓦' ̇
 Bracket (x , d) = L x × R (x + d)

 step-keeps-brackets : (s : ♭ (ℚ × ℚ))
                     → Bracket (♭-counit s)
                     → Bracket (♭-counit (step s))
 step-keeps-brackets (p ^♭) (l , r) = γ (choice (mid p))
  where
   γ : (z : L (mid p) ∔ R (mid p)) → Bracket (next (side (mid p) z) p)
   γ (inl l') = l' , transport R (add-two-halves (pr₁ p) (pr₂ p) ⁻¹) r
   γ (inr r') = l , r'

\end{code}

The bisection of [α , β], and the crisp real it determines, as in
gist.RealCohesion.CrispConnectedness.

\begin{code}

 module _ (@♭ α β : ℚ) where

  D : ℚ
  D = nonneg-part (β - α)

  start : ♭ (ℚ × ℚ)
  start = (α , D) ^♭

  stage : ℕ → ♭ (ℚ × ℚ)
  stage = bisection start

  left length : ℕ → ℚ
  left n   = pr₁ (♭-counit (stage n))
  length n = pr₂ (♭-counit (stage n))

  open halving-sequence.nonneg length (λ n → step-halves (stage n))
        (nonneg-part-is-nonneg (β - α))
   using () renaming (is-nonneg to length-nonneg) public
  open halving-sequence-bounds length (λ n → step-halves (stage n)) D
        (nonneg-part-is-nonneg (β - α)) (ℚ≤-refl D)
   using () renaming
    (bound to length-bound ; becomes-small to lengths-become-small)
   public

  intervals : Nested-Intervals
  intervals = record
               { left                 = left
                ; length               = length
                ; length-nonneg        = length-nonneg
                ; left-grows           =
                 λ n → step-left-grows (stage n) (length-nonneg n)
                ; right-shrinks        =
                 λ n → step-right-shrinks (stage n) (length-nonneg n)
                ; lengths-become-small = lengths-become-small
                }

  τ : ℝ
  τ = limit intervals

  right-end : α < β → α + D ＝ β
  right-end α<β =
   ap (α +_) (nonneg-part-of-positive (β - α) (ℚ<-difference-positive α β α<β))
                ∙ add-difference α β

  brackets : Bracket (α , D) → (n : ℕ) → Bracket (♭-counit (stage n))
  brackets b₀ 0        = b₀
  brackets b₀ (succ n) = step-keeps-brackets (stage n) (brackets b₀ n)

\end{code}

If W is open at crisp points and holds at τ, then W holds at both ends
of a stage of the bisection. So W fails at τ if it cannot hold at both
ends of a bracket.

\begin{code}

  limit-is-not-in : {𝓣 : Universe} (W : ℝ → 𝓣 ̇ )
                  → ((@♭ t : ℝ) → W t → Holds-Near W t)
                  → ((e : ℚ × ℚ) → Bracket e
                                 → W (ιₐ (pr₁ e)) → W (ιₐ (pr₁ e + pr₂ e))
                                 → 𝟘 {𝓤₀})
                  → Bracket (α , D) → ¬ W τ
  limit-is-not-in W W-is-open clash b₀ w = ∥∥-rec 𝟘-is-prop γ (W-is-open τ w)
   where
    γ : (Σ (r , r') ꞉ ℚ × ℚ ,
          (r < τ) × (τ < r') × ((@♭ s : ℝ) → r < s → s < r' → W s))
      → 𝟘 {𝓤₀}
    γ ((r , r') , a , b , h) =
     ∥∥-rec 𝟘-is-prop
      (λ (n , k , k') → δ n (ends-in W r r' h (stage n) (length-nonneg n) k k'))
      (intervals-around-the-limit intervals r r' a b)
     where
      δ : (n : ℕ)
        → W (ιₐ (pr₁ (♭-counit (stage n))))
        × W (ιₐ (pr₁ (♭-counit (stage n)) + pr₂ (♭-counit (stage n))))
        → 𝟘 {𝓤₀}
      δ n (w₀ , w₁) = clash (♭-counit (stage n)) (brackets b₀ n) w₀ w₁

\end{code}

Crisp functions are continuous at crisp points, by hypothesis. So the
points where f is below c, and the points where f is above c, are open
at crisp points. Compare below-is-open and above-is-open in
gist.RealCohesion.CrispExactIVT, which take continuity from crisp
excluded middle for 𝓤₁.

\begin{code}

module _ (continuity : Crisp-Real-Continuity) where

 below-is-open : (@♭ f : ℝ → ℝ) (c : ℝ) (@♭ t : ℝ)
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
                  (continuity f t L w p o)

 above-is-open : (@♭ f : ℝ → ℝ) (c : ℝ) (@♭ t : ℝ)
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
                  (continuity f t w U o' p)

\end{code}

Crisp rational witnesses, at arbitrary points, by rational detection.
These are rational-below and rational-above of
gist.RealCohesion.CrispExactIVT, which do not use the crisp excluded
middle that is in scope there.

\begin{code}

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

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

The intermediate value theorem for crisp f and c and crisp rational
end points, from a crisp choice of f q ≤ c or c ≤ f q at each crisp
rational q. The inequalities at the end points need not be strict.

\begin{code}

flip-sum : {𝓦 𝓦' : Universe} {A : 𝓦 ̇ } {B : 𝓦' ̇ } → A ∔ B → B ∔ A
flip-sum (inl a) = inr a
flip-sum (inr b) = inl b

module _ (@♭ f : ℝ → ℝ)
         (@♭ c : ℝ)
         (@♭ choice : (@♭ q : ℚ) → (f (ιₐ q) ≤ c) ∔ (c ≤ f (ιₐ q)))
       where

 private
  Lo Hi : ℚ → 𝓤₀ ̇
  Lo q = f (ιₐ q) ≤ c
  Hi q = c ≤ f (ιₐ q)

  choice' : (@♭ q : ℚ) → Hi q ∔ Lo q
  choice' q = flip-sum (choice q)

 module _ (continuity : Crisp-Real-Continuity) where

  private
   not-below-and-at-least : (x : ℝ) → f x < c → c ≤ f x → 𝟘 {𝓤₀}
   not-below-and-at-least x l m = ℝ-less-than-or-equal-not-greater c (f x) m l

   not-above-and-at-most : (x : ℝ) → c < f x → f x ≤ c → 𝟘 {𝓤₀}
   not-above-and-at-most x l m = ℝ-less-than-or-equal-not-greater (f x) c m l

  root-of-increase : (@♭ α β : ℚ) → α < β
                   → f (ιₐ α) ≤ c → c ≤ f (ιₐ β)
                   → Σ x ꞉ ℝ , f x ＝ c
  root-of-increase α β α<β l m =
   τ Lo Hi choice α β ,
   ℝ<-tight (f (τ Lo Hi choice α β)) c
    (limit-is-not-in Lo Hi choice α β (λ s → f s < c)
      (λ t → below-is-open continuity f c t)
      (λ e b w w' → not-below-and-at-least (ιₐ (pr₁ e + pr₂ e)) w' (pr₂ b))
      b₀)
    (limit-is-not-in Lo Hi choice α β (λ s → c < f s)
      (λ t → above-is-open continuity f c t)
      (λ e b w w' → not-above-and-at-most (ιₐ (pr₁ e)) w (pr₁ b))
      b₀)
   where
    b₀ : Bracket Lo Hi choice (α , D Lo Hi choice α β)
    b₀ = l , transport Hi (right-end Lo Hi choice α β α<β ⁻¹) m

  root-of-decrease : (@♭ α β : ℚ) → α < β
                   → c ≤ f (ιₐ α) → f (ιₐ β) ≤ c
                   → Σ x ꞉ ℝ , f x ＝ c
  root-of-decrease α β α<β l m =
   τ Hi Lo choice' α β ,
   ℝ<-tight (f (τ Hi Lo choice' α β)) c
    (limit-is-not-in Hi Lo choice' α β (λ s → f s < c)
      (λ t → below-is-open continuity f c t)
      (λ e b w w' → not-below-and-at-least (ιₐ (pr₁ e)) w (pr₁ b))
      b₀)
    (limit-is-not-in Hi Lo choice' α β (λ s → c < f s)
      (λ t → above-is-open continuity f c t)
      (λ e b w w' → not-above-and-at-most (ιₐ (pr₁ e + pr₂ e)) w' (pr₂ b))
      b₀)
   where
    b₀ : Bracket Hi Lo choice' (α , D Hi Lo choice' α β)
    b₀ = l , transport Lo (right-end Hi Lo choice' α β α<β ⁻¹) m

  root-between-crisp-rationals : (@♭ α β : ℚ)
                               → f (ι α) < c → c < f (ι β)
                               → Σ x ꞉ ℝ , f x ＝ c
  root-between-crisp-rationals α β l m = ε (ℚ-trichotomous α β)
   where
    l' : f (ιₐ α) ≤ c
    l' = ℝ<-gives-≤ (f (ιₐ α)) c (transport (λ - → f - < c) (ιₐ-is-ι α ⁻¹) l)

    m' : c ≤ f (ιₐ β)
    m' = ℝ<-gives-≤ c (f (ιₐ β)) (transport (λ - → c < f -) (ιₐ-is-ι β ⁻¹) m)

    ε : (α < β) ∔ (α ＝ β) ∔ (β < α) → Σ x ꞉ ℝ , f x ＝ c
    ε (inl α<β)       = root-of-increase α β α<β l' m'
    ε (inr (inl e))   = 𝟘-elim (ℝ<-asymmetric (f (ι α)) c l
                                 (transport (λ - → c < f (ι -)) (e ⁻¹) m))
    ε (inr (inr β<α)) = root-of-decrease β α β<α m' l'

\end{code}

The theorem, for arbitrary points a and b, by rational detection.

\begin{code}

  module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

   exact-IVT-from-choices : (a b : ℝ) → f a < c → c < f b → ∃ x ꞉ ℝ , f x ＝ c
   exact-IVT-from-choices a b l m =
    ∥∥-rec ∃-is-prop γ (rational-below ν f c a l)
    where
     γ : (Σ α ꞉ ♭ ℚ , f (ι (♭-counit α)) < c) → ∃ x ꞉ ℝ , f x ＝ c
     γ ((α ^♭) , l') = ∥∥-functor δ (rational-above ν f c b m)
      where
       δ : (Σ β ꞉ ♭ ℚ , c < f (ι (♭-counit β))) → Σ x ꞉ ℝ , f x ＝ c
       δ ((β ^♭) , m') = root-between-crisp-rationals α β l' m'

\end{code}

The three hypotheses, and the theorem from each of them.

\begin{code}

Crisp-Order-Is-Decidable : 𝓤₁ ̇
Crisp-Order-Is-Decidable = (@♭ x y : ℝ) → (x < y) ∔ ¬ (x < y)

Crisp-Order-Is-Total : 𝓤₁ ̇
Crisp-Order-Is-Total = (@♭ x y : ℝ) → (x ≤ y) ∔ (y ≤ x)

crisp-EM-gives-decidable-order : (@♭ cem : Crisp-EM 𝓤₀)
                               → Crisp-Order-Is-Decidable
crisp-EM-gives-decidable-order cem x y = cem (x < y) (<-is-prop x y)

decidable-order-gives-total-order : Crisp-Order-Is-Decidable
                                  → Crisp-Order-Is-Total
decidable-order-gives-total-order d x y = γ (d x y)
 where
  γ : (x < y) ∔ ¬ (x < y) → (x ≤ y) ∔ (y ≤ x)
  γ (inl l) = inl (ℝ<-gives-≤ x y l)
  γ (inr n) = inr (ℝ-not-less-is-greater-or-equal x y n)

module _ (continuity : Crisp-Real-Continuity)
         (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v)
       where

 exact-IVT-from-total-order : (@♭ total : Crisp-Order-Is-Total)
                              (@♭ f : ℝ → ℝ) (@♭ c : ℝ) (a b : ℝ)
                            → f a < c → c < f b → ∃ x ꞉ ℝ , f x ＝ c
 exact-IVT-from-total-order total f c =
  exact-IVT-from-choices f c (λ q → total (f (ιₐ q)) c) continuity ν

 exact-IVT-from-decidable-order : (@♭ d : Crisp-Order-Is-Decidable)
                                  (@♭ f : ℝ → ℝ) (@♭ c : ℝ) (a b : ℝ)
                                → f a < c → c < f b → ∃ x ꞉ ℝ , f x ＝ c
 exact-IVT-from-decidable-order d =
  exact-IVT-from-total-order (decidable-order-gives-total-order d)

 exact-IVT-from-crisp-EM₀ : (@♭ cem : Crisp-EM 𝓤₀)
                            (@♭ f : ℝ → ℝ) (@♭ c : ℝ) (a b : ℝ)
                          → f a < c → c < f b → ∃ x ꞉ ℝ , f x ＝ c
 exact-IVT-from-crisp-EM₀ cem =
  exact-IVT-from-decidable-order (crisp-EM-gives-decidable-order cem)

\end{code}
