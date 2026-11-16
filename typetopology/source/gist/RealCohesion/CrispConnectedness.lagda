Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

Connectedness of rational intervals, for crisp predicates on crisp
points.

Let U be a crisp family of propositions on ℝ, and α < β crisp
rationals. Suppose that U and its negation are both open at the crisp
points of [α , β]: if U t, or ¬ U t, for a crisp t in [α , β], then U
holds, or fails, at all crisp points of some rational interval around
t.

Then U α if and only if U β. This is the classical connectedness of
the interval, restricted to crisp points, and we prove it classically
from crisp excluded middle, by bisection: if U holds at exactly one of
α and β, we halve [α , β] repeatedly, keeping a subinterval whose
endpoints disagree about U. The choices are made by crisp excluded
middle, at crisp points, and we keep the successive intervals crisp by
computing them in ♭ (ℚ × ℚ). The intervals determine a crisp real τ
(gist.RealCohesion.NestedIntervals). Whether or not U τ holds, the
small intervals around τ contain a whole stage of the bisection, whose
endpoints would then agree.

Internally we evaluate U at rational points through the abstract
embedding ιₐ of gist.RealCohesion.RationalPoints, for the reason
explained there.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.CrispConnectedness
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Addition
open import Rationals.Limits fe pe pt
open import Rationals.MinMax
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order

open import Rationals.Type
open import UF.Base
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.CrispDecisions
open import gist.RealCohesion.NestedIntervals fe pe pt
open import gist.RealCohesion.RationalArithmetic
open import gist.RealCohesion.RationalLimits fe pe pt
open import gist.RealCohesion.RationalPoints fe pe pt

open PropositionalTruncation pt

\end{code}


The bisection. A state is a crisp pair (x , d), standing for the
interval [x , x + d], with d ≥ 0. A step decides U at x and at the midpoint, and
keeps the half whose endpoints disagree, if U disagrees at x and x + d.

\begin{code}

module _ {@♭ 𝓦 : Universe}
         (@♭ cem : Crisp-EM 𝓦)
         (@♭ U : ℝ → 𝓦 ̇ )
         (@♭ U-is-prop : (x : ℝ) → is-prop (U x))
       where

 V : ℚ → 𝓦 ̇
 V x = U (ιₐ x)

 V-is-prop : (x : ℚ) → is-prop (V x)
 V-is-prop x = U-is-prop (ιₐ x)

 test : (@♭ x : ℚ) → 𝟚
 test = crisp-test cem V V-is-prop

 agree : 𝟚 → 𝟚 → 𝟚
 agree ₀ ₀ = ₁
 agree ₀ ₁ = ₀
 agree ₁ ₀ = ₀
 agree ₁ ₁ = ₁

 choose : 𝟚 → 𝟚 → ℚ → ℚ → ℚ × ℚ
 choose b b' x d = (halve (agree b b') x d , half d)

 left-bit mid-bit : (@♭ p : ℚ × ℚ) → 𝟚
 left-bit p = test (pr₁ p)
 mid-bit  p = test (pr₁ p + half (pr₂ p))

 step : ♭ (ℚ × ℚ) → ♭ (ℚ × ℚ)
 step (p ^♭) = (choose (left-bit p) (mid-bit p) (pr₁ p) (pr₂ p)) ^♭

 bisection : ♭ (ℚ × ℚ) → ℕ → ♭ (ℚ × ℚ)
 bisection s 0        = s
 bisection s (succ n) = step (bisection s n)

\end{code}

The effect of a step on the interval.

\begin{code}

 choose-length : (b b' : 𝟚) (x d : ℚ) → pr₂ (choose b b' x d) ＝ half d
 choose-length b b' x d = refl

 choose-left-grows : (b b' : 𝟚) (x d : ℚ) → 0ℚ ≤ d → x ≤ pr₁ (choose b b' x d)
 choose-left-grows b b' = halve-grows (agree b b')

 choose-right-shrinks : (b b' : 𝟚) (x d : ℚ) → 0ℚ ≤ d
                      → pr₁ (choose b b' x d) + pr₂ (choose b b' x d) ≤ x + d
 choose-right-shrinks b b' = halve-shrinks (agree b b')

 step-halves : (s : ♭ (ℚ × ℚ))
             → pr₂ (♭-counit (step s)) ＝ half (pr₂ (♭-counit s))
 step-halves (p ^♭) = choose-length (left-bit p) (mid-bit p) (pr₁ p) (pr₂ p)

 step-left-grows : (s : ♭ (ℚ × ℚ)) → 0ℚ ≤ pr₂ (♭-counit s)
                 → pr₁ (♭-counit s) ≤ pr₁ (♭-counit (step s))
 step-left-grows (p ^♭) =
  choose-left-grows (left-bit p) (mid-bit p) (pr₁ p) (pr₂ p)

 step-right-shrinks : (s : ♭ (ℚ × ℚ)) → 0ℚ ≤ pr₂ (♭-counit s)
                    → pr₁ (♭-counit (step s)) + pr₂ (♭-counit (step s))
                      ≤ pr₁ (♭-counit s) + pr₂ (♭-counit s)
 step-right-shrinks (p ^♭) =
  choose-right-shrinks (left-bit p) (mid-bit p) (pr₁ p) (pr₂ p)

\end{code}

The effect of a step on the disagreement of U at the endpoints.

\begin{code}

 Ends-Disagree : ℚ × ℚ → 𝓦 ̇
 Ends-Disagree (x , d) = V x ↔ ¬ V (x + d)

 step-keeps-disagreement : (s : ♭ (ℚ × ℚ))
                         → Ends-Disagree (♭-counit s)
                         → Ends-Disagree (♭-counit (step s))
 step-keeps-disagreement (p ^♭) disagree =
  γ (left-bit p) (mid-bit p) refl refl
  where
   γ : (b b' : 𝟚)
     → left-bit p ＝ b
     → mid-bit p ＝ b'
     → Ends-Disagree (choose b b' (pr₁ p) (pr₂ p))
   γ ₀ ₀ e e' =
    (λ u → 𝟘-elim (crisp-test-₀ cem V V-is-prop (pr₁ p + half (pr₂ p)) e' u)) ,
                (λ ν → 𝟘-elim (crisp-test-₀ cem V V-is-prop (pr₁ p) e
                                (rl-implication disagree
                                  (transport (λ - → ¬ V -)
                                    (add-two-halves (pr₁ p) (pr₂ p)) ν))))
   γ ₀ ₁ e e' = (λ u → 𝟘-elim (crisp-test-₀ cem V V-is-prop (pr₁ p) e u)) ,
                (λ ν → 𝟘-elim
                  (ν (crisp-test-₁ cem V V-is-prop (pr₁ p + half (pr₂ p)) e')))
   γ ₁ ₀ e e' = (λ _ → crisp-test-₀ cem V V-is-prop (pr₁ p + half (pr₂ p)) e') ,
                (λ _ → crisp-test-₁ cem V V-is-prop (pr₁ p) e)
   γ ₁ ₁ e e' =
    (λ _ → transport (λ - → ¬ V -) (add-two-halves (pr₁ p) (pr₂ p) ⁻¹)
             (lr-implication disagree (crisp-test-₁ cem V V-is-prop (pr₁ p) e)))
              ,
                (λ _ → crisp-test-₁ cem V V-is-prop (pr₁ p + half (pr₂ p)) e')

\end{code}

The bisection of [α , β], and the crisp real it determines. We start
from the interval [α , α + max 0 (β - α)], so that the construction makes
sense, and the limit is crisp, without a proof of α < β; that proof is
only needed afterwards, to see that α + max 0 (β - α) ＝ β.

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

  α-below-τ : ι α ≤ τ
  α-below-τ q l = below-the-limit intervals 0 q l

  module _ (α<β : α < β) where

   right-end : α + D ＝ β
   right-end =
    ap (α +_) (nonneg-part-of-positive (β - α) (ℚ<-difference-positive α β α<β))
             ∙ add-difference α β

   τ-below-β : τ ≤ ι β
   τ-below-β q l = transport (q <_) right-end
                    (below-the-limit-gives-below-right intervals 0 q l)

\end{code}

The theorem. We assume that U and its negation are both open at the
crisp points of [α , β]: each crisp point where U holds, or fails, has
a rational neighbourhood on whose crisp points U holds, or fails,
respectively.

\begin{code}

  Open-At-Crisp-Points : (ℝ → 𝓦 ̇ ) → 𝓤₁ ⊔ 𝓦 ̇
  Open-At-Crisp-Points W =
     (@♭ t : ℝ) → ι α ≤ t → t ≤ ι β → W t
   →
   ∃ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r') × ((@♭ s : ℝ) → r < s → s < r' → W s)

  module _ (α<β        : α < β)
           (U-is-open  : Open-At-Crisp-Points U)
           (¬U-is-open : Open-At-Crisp-Points (λ t → ¬ U t))
         where

   private
    disagreement : Ends-Disagree (α , D)
                 → (n : ℕ) → Ends-Disagree (♭-counit (stage n))
    disagreement d₀ 0        = d₀
    disagreement d₀ (succ n) =
     step-keeps-disagreement (stage n) (disagreement d₀ n)

    ends-in : (W : ℝ → 𝓦 ̇ ) (r r' : ℚ)
            → ((@♭ s : ℝ) → r < s → s < r' → W s)
            → (s : ♭ (ℚ × ℚ))
            → 0ℚ ≤ pr₂ (♭-counit s)
            → r < pr₁ (♭-counit s)
            → pr₁ (♭-counit s) + pr₂ (♭-counit s) < r'
            → W (ιₐ (pr₁ (♭-counit s)))
            × W (ιₐ (pr₁ (♭-counit s) + pr₂ (♭-counit s)))
    ends-in W r r' f (p ^♭) l a b =
     f (ιₐ (pr₁ p)) (ιₐ-lower r (pr₁ p) a)
       (ιₐ-upper (pr₁ p) r' (ℚ≤-<-trans (pr₁ p) (pr₁ p + pr₂ p) r' x≤x+d b)) ,
     f (ιₐ (pr₁ p + pr₂ p))
       (ιₐ-lower r (pr₁ p + pr₂ p)
         (ℚ<-≤-trans r (pr₁ p) (pr₁ p + pr₂ p) a x≤x+d))
       (ιₐ-upper (pr₁ p + pr₂ p) r' b)
     where
      x≤x+d : pr₁ p ≤ pr₁ p + pr₂ p
      x≤x+d = ℚ≤-addition-preserves-order'' (pr₁ p) (pr₂ p) l

\end{code}

If W is open at the crisp points of [α , β] and holds at τ, then W
holds at both ends of one of the nested intervals, which contradicts
their disagreement when W is U and when W is its negation.

\begin{code}

    τ-is-not-in : (W : ℝ → 𝓦 ̇ )
                → Open-At-Crisp-Points W
                → ((e : ℚ × ℚ) → Ends-Disagree e
                               → W (ιₐ (pr₁ e)) → W (ιₐ (pr₁ e + pr₂ e))
                               → 𝟘 {𝓤₀})
                → Ends-Disagree (α , D) → ¬ W τ
    τ-is-not-in W W-is-open clash d₀ w =
     ∥∥-rec 𝟘-is-prop γ (W-is-open τ α-below-τ (τ-below-β α<β) w)
     where
      γ : (Σ (r , r') ꞉ ℚ × ℚ ,
            (r < τ) × (τ < r') × ((@♭ s : ℝ) → r < s → s < r' → W s))
        → 𝟘 {𝓤₀}
      γ ((r , r') , a , b , f) =
       ∥∥-rec 𝟘-is-prop
        (λ (n , k , k') →
          δ n (ends-in W r r' f (stage n) (length-nonneg n) k k'))
        (intervals-around-the-limit intervals r r' a b)
       where
        δ : (n : ℕ)
          → W (ιₐ (pr₁ (♭-counit (stage n))))
          × W (ιₐ (pr₁ (♭-counit (stage n)) + pr₂ (♭-counit (stage n))))
          → 𝟘 {𝓤₀}
        δ n (w₀ , w₁) = clash (♭-counit (stage n)) (disagreement d₀ n) w₀ w₁

   ends-cannot-disagree : Ends-Disagree (α , D) → 𝟘 {𝓤₀}
   ends-cannot-disagree d₀ =
    cases (τ-is-not-in U U-is-open (λ e d u u' → lr-implication d u u') d₀)
          (τ-is-not-in (λ t → ¬ U t) ¬U-is-open
            (λ e d ν ν' → ν (rl-implication d ν')) d₀)
          (cem (U τ) (U-is-prop τ))

   private
    V-at-ends : V α ↔ V β
    V-at-ends = forward , backward
     where
      to-β : V (α + D) → V β
      to-β = transport V (right-end α<β)

      from-β : V β → V (α + D)
      from-β = transport V (right-end α<β ⁻¹)

      forward : V α → V β
      forward v = cases id
                   (λ ν → 𝟘-elim (ends-cannot-disagree
                                   ((λ _ ν' → ν (to-β ν')) , (λ _ → v))))
                   (cem (V β) (V-is-prop β))

      backward : V β → V α
      backward v = cases id
                    (λ ν → 𝟘-elim (ends-cannot-disagree
                                    ((λ v' → 𝟘-elim (ν v')) ,
                                     (λ ν' → 𝟘-elim (ν' (from-β v))))))
                    (cem (V α) (V-is-prop α))

   crisp-interval-is-connected : U (ι α) ↔ U (ι β)
   crisp-interval-is-connected =
    (λ u → transport U (ιₐ-is-ι β) (lr-implication V-at-ends
                                      (transport U (ιₐ-is-ι α ⁻¹) u))) ,
    (λ u → transport U (ιₐ-is-ι α) (rl-implication V-at-ends
                                      (transport U (ιₐ-is-ι β ⁻¹) u)))

\end{code}
