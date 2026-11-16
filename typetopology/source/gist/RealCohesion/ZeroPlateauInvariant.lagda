Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 26 October 2026. See the AI disclosure in
gist.RealCohesion.index. The argument is the analytic part of the
counterexample in the research notes [1, Section 5], by Claude Opus,
in the form proposed by GPT-6 Astra's gameplan (25 October 2026) [2].

The zero-plateau invariant.

Let g : ℝ → ℝ be crisp, with g 0 ＝ 0. On the crisp points of the
kernel N of g, the pairs (p , q) with g p ＝ g q, consider the parity
of the number of coordinates equal to 0,

  h (p , q) = δ p ⊕ δ q,

as in gist.RealCohesion.RealKernelCocycle. We prove that h is
invariant along crisp real paths in N, assuming crisp excluded middle,
that crisp functions are continuous at crisp points
(Crisp-Real-Continuity, from gist.RealCohesion.CrispRealAnalysis), and
the following two properties of g.

 * g oscillates at 0: arbitrarily close to 0, on both sides, there are
   rational intervals on which g is positive, and rational intervals
   on which g is negative.

 * Every crisp nonzero zero of g lies in a plateau: a rational
   interval [lo , hi] not containing 0, on which g is 0, and next to
   which g has a strict sign on each side, on rational intervals.

The main step is the following. Let p , q : ℝ → ℝ be crisp, with
g (p t) ＝ g (q t) for all t, and let [lo , hi] be a plateau. The
crisp predicate

  U t = (p t ＝ 0) × (q t is in [lo , hi])

is open and co-open at the crisp points of [0 , 1], so it holds at 0
if and only if it holds at 1, by the connectedness of the interval
(gist.RealCohesion.CrispConnectedness). It is co-open by continuity.
It is open because near a point of the plateau, g has a weak sign, so
g ∘ p has this weak sign near a parameter t with U t. Then p cannot
leave 0, since arbitrarily close to 0 there are intervals on which g
has the opposite sign (gist.RealCohesion.CrispRealAnalysis, staying at
zero). Hence g ∘ q is 0 near t, and q stays in the plateau.

A case analysis on the four values of δ at the ends of the path then
shows that h is invariant.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

[2] GPT-6 Astra. Gameplan for Opus: a subset of the Dedekind reals
    whose shape is not a set, 25 October 2026.
    references/A32-subset-shape-gameplan.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.ZeroPlateauInvariant
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Order
open import Rationals.Type
open import UF.Base
open import UF.Powerset
open import UF.Subsingletons-FunExt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.CrispConnectedness fe pe pt
 using (Open-At-Crisp-Points ; crisp-interval-is-connected)
open import gist.RealCohesion.CrispDecisions
open import gist.RealCohesion.CrispRationals
open import gist.RealCohesion.CrispRealAnalysis fe pe pt
open import gist.RealCohesion.RealKernelCocycle fe pe pt
open import gist.RealCohesion.RationalPoints fe pe pt using (0ℝₐ ; 0ℝₐ-is-0ℝ)
open import gist.RealCohesion.RealPathDescent fe pe pt

open PropositionalTruncation pt

\end{code}

Plateaux, oscillation at 0, and the classification of zeros. A real
number x lies in [lo , hi] when ¬ (x < lo) and ¬ (hi < x). In the
fields of the records, 0 is the abstract copy 0ℝₐ of 0ℝ from
gist.RealCohesion.RationalPoints, because Agda normalizes the types of
record fields; the functions plateau-flat and oscillation-at-zero
restate these fields with 0ℝ.

\begin{code}

record Plateau (g : ℝ → ℝ) (lo hi : ℚ) : 𝓤₁ ̇ where
 field
  lo' hi'        : ℚ
  lo'<lo         : lo' < lo
  lo<hi          : lo < hi
  hi<hi'         : hi < hi'
  away-from-zero : (0ℚ < lo) ∔ (hi < 0ℚ)
  sign-below     : 𝟚
  sign-above     : 𝟚
  flat           : (x : ℝ) → ¬ (x < lo) → ¬ (hi < x) → g x ＝ 0ℝₐ
  signed-below   : (x : ℝ) → lo' < x → x < lo → Has-Sign sign-below (g x)
  signed-above   : (x : ℝ) → hi < x → x < hi' → Has-Sign sign-above (g x)

plateaux-avoid-zero : {g : ℝ → ℝ} {lo hi : ℚ} → Plateau g lo hi
                    → (x : ℝ) → ¬ (x < lo) → ¬ (hi < x) → ¬ (x ＝ 0ℝ)
plateaux-avoid-zero {g} {lo} {hi} C x m m' e = γ (Plateau.away-from-zero C)
 where
  γ : (0ℚ < lo) ∔ (hi < 0ℚ) → 𝟘
  γ (inl l) = m  (transport (λ (y : ℝ) → y < lo) (e ⁻¹) l)
  γ (inr l) = m' (transport (λ (y : ℝ) → hi < y) (e ⁻¹) l)

record Oscillates-At-Zero (g : ℝ → ℝ) : 𝓤₁ ̇ where
 field
  value-at-zero  : g 0ℝₐ ＝ 0ℝₐ
  signed-right   : (σ : 𝟚) (e : ℚ) → 0ℚ < e
                 → ∃ (a , b) ꞉ ℚ × ℚ , (0ℚ < a) × (a < b) × (b < e)
                                     × ((x : ℝ) → a < x → x < b
                                        → Has-Sign σ (g x))
  signed-left    : (σ : 𝟚) (e : ℚ) → e < 0ℚ
                 → ∃ (a , b) ꞉ ℚ × ℚ , (e < a) × (a < b) × (b < 0ℚ)
                                     × ((x : ℝ) → a < x → x < b
                                        → Has-Sign σ (g x))

plateau-flat : {g : ℝ → ℝ} {lo hi : ℚ} → Plateau g lo hi
             → (x : ℝ) → ¬ (x < lo) → ¬ (hi < x) → g x ＝ 0ℝ
plateau-flat C x m m' = Plateau.flat C x m m' ∙ 0ℝₐ-is-0ℝ

oscillation-at-zero : {g : ℝ → ℝ} → Oscillates-At-Zero g → g 0ℝ ＝ 0ℝ
oscillation-at-zero {g} osc = ap g (0ℝₐ-is-0ℝ ⁻¹)
                            ∙ Oscillates-At-Zero.value-at-zero osc
                            ∙ 0ℝₐ-is-0ℝ

Zeros-Lie-In-Plateaux : (ℝ → ℝ) → 𝓤₁ ̇
Zeros-Lie-In-Plateaux g =
   (@♭ z : ℝ) → g z ＝ 0ℝ → ¬ (z ＝ 0ℝ)
 → ∃ (lo , hi) ꞉ ℚ × ℚ , Plateau g lo hi × ¬ (z < lo) × ¬ (hi < z)

\end{code}

A weak sign near each point of a plateau. Near a point x of [lo , hi]
there is a rational interval on which g never has the sign opposite to
some σ, and whose zeros lie in [lo , hi].

\begin{code}

module _ {g : ℝ → ℝ} {lo hi : ℚ} (C : Plateau g lo hi) where

 open Plateau C

 private
  by-cases : {A : 𝓤 ̇ } → (A → 𝟘 {𝓤₀}) → (¬ A → 𝟘 {𝓤₀}) → 𝟘 {𝓤₀}
  by-cases f g = g f

 Weak-Sign-Near-Plateau : ℝ → 𝓤₁ ̇
 Weak-Sign-Near-Plateau y =
  Σ (e , e') ꞉ ℚ × ℚ , Σ σ ꞉ 𝟚 , (e < y) × (y < e')
                    × ((x : ℝ) → e < x → x < e' → ¬ Has-Sign (opposite σ) (g x))
                    × ((x : ℝ) → e < x → x < e' → g x ＝ 0ℝ
                       → ¬ (x < lo) × ¬ (hi < x))

 weak-sign-below-hi : (y : ℝ) → ¬ (y < lo) → y < hi → Weak-Sign-Near-Plateau y
 weak-sign-below-hi y m l =
  (lo' , hi) , sign-below , located-above y lo' lo lo'<lo m , l , I , II
  where
   I : (x : ℝ) → lo' < x → x < hi → ¬ Has-Sign (opposite sign-below) (g x)
   I x a b s = by-cases
                (λ (c : x < lo) →
                  signs-are-exclusive sign-below (g x) (signed-below x a c) s)
                (λ (c : ¬ (x < lo)) → zero-has-no-sign (opposite sign-below)
                                       (transport
                                         (Has-Sign (opposite sign-below))
                                         (plateau-flat C x c (λ d →
                                           not-below-and-above x hi d b)) s))

   II : (x : ℝ) → lo' < x → x < hi → g x ＝ 0ℝ → ¬ (x < lo) × ¬ (hi < x)
   II x a b e = (λ c → zero-has-no-sign sign-below
                         (transport (Has-Sign sign-below) e
                           (signed-below x a c))) ,
                (λ d → not-below-and-above x hi d b)

 weak-sign-above-lo : (y : ℝ) → lo < y → ¬ (hi < y) → Weak-Sign-Near-Plateau y
 weak-sign-above-lo y l m =
  (lo , hi') , sign-above , l , located-below y hi hi' hi<hi' m , I , II
  where
   I : (x : ℝ) → lo < x → x < hi' → ¬ Has-Sign (opposite sign-above) (g x)
   I x a b s = by-cases
                (λ (c : hi < x) →
                  signs-are-exclusive sign-above (g x) (signed-above x c b) s)
                (λ (c : ¬ (hi < x)) → zero-has-no-sign (opposite sign-above)
                                       (transport
                                         (Has-Sign (opposite sign-above))
                                         (plateau-flat C x (λ d →
                                           not-below-and-above x lo a d) c) s))

   II : (x : ℝ) → lo < x → x < hi' → g x ＝ 0ℝ → ¬ (x < lo) × ¬ (hi < x)
   II x a b e = (λ d → not-below-and-above x lo a d) ,
                (λ c → zero-has-no-sign sign-above
                         (transport (Has-Sign sign-above) e
                           (signed-above x c b)))

\end{code}

The predicate U of the main step, defined at top level so that it is
crisp when p, q, lo and hi are.

\begin{code}

In-Plateau-At-Zero : (ℝ → ℝ) → (ℝ → ℝ) → ℚ → ℚ → ℝ → 𝓤₁ ̇
In-Plateau-At-Zero p q lo hi t = (p t ＝ 0ℝ) × ¬ (q t < lo) × ¬ (hi < q t)

In-Plateau-At-Zero-is-prop : (p q : ℝ → ℝ) (lo hi : ℚ) (t : ℝ)
                           → is-prop (In-Plateau-At-Zero p q lo hi t)
In-Plateau-At-Zero-is-prop p q lo hi t =
 ×-is-prop ℝ-is-set
  (×-is-prop (negations-are-props fe) (negations-are-props fe))

\end{code}

The main step.

\begin{code}

module _ (@♭ cem : Crisp-EM 𝓤₁)
         (@♭ continuity : Crisp-Real-Continuity)
         (@♭ g : ℝ → ℝ)
         (@♭ osc : Oscillates-At-Zero g)
       where

 open Oscillates-At-Zero osc

 private
  cem' : Crisp-EM 𝓤₀
  cem' = cem₀ cem

  g-vanishes-at-zero : g 0ℝ ＝ 0ℝ
  g-vanishes-at-zero = oscillation-at-zero osc

 module _ (@♭ p q : ℝ → ℝ)
          (same-height : (t : ℝ) → g (p t) ＝ g (q t))
          (@♭ lo hi : ℚ)
          (C : Plateau g lo hi)
        where

  private
   U-is-open : Open-At-Crisp-Points cem (In-Plateau-At-Zero p q lo hi)
                (In-Plateau-At-Zero-is-prop p q lo hi) 0ℚ 1ℚ
                (In-Plateau-At-Zero p q lo hi)
   U-is-open t _ _ (pt-is-0 , m , m') =
    γ (cem' (q t < hi) (∈-is-prop (upper-cut-of (q t)) hi))
    where
     κ : Weak-Sign-Near-Plateau C (q t)
       → Holds-Near (In-Plateau-At-Zero p q lo hi) t
     κ ((e , e') , σ , e<qt , qt<e' , weak , zeros) =
      ∥∥-functor ε (continuity q t e e' e<qt qt<e')
      where
       ε : (Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                               × ((@♭ s : ℝ) → r < s → s < r'
                                  → (e < q s) × (q s < e')))
         → Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                              × ((@♭ s : ℝ) → r < s → s < r'
                                 → In-Plateau-At-Zero p q lo hi s)
       ε ((r , r') , r<t , t<r' , k) = (r , r') , r<t , t<r' , ζ
        where
         avoids : (a b : ℚ)
                → ((x : ℝ) → a < x → x < b → Has-Sign (opposite σ) (g x))
                → Avoids p r r' a b
         avoids a b signed s c d (a<ps , ps<b) =
          weak (q s) (pr₁ (k s c d)) (pr₂ (k s c d))
           (transport (Has-Sign (opposite σ)) (same-height s)
             (signed (p s) a<ps ps<b))

         right : (e₀ : ℚ) → 0ℚ < e₀
               → ∃ (a , b) ꞉ ℚ × ℚ ,
                   (0ℚ < a) × (a < b) × (b < e₀) × Avoids p r r' a b
         right e₀ l = ∥∥-functor θ (signed-right (opposite σ) e₀ l)
          where
           θ : (Σ (a , b) ꞉ ℚ × ℚ , (0ℚ < a) × (a < b) × (b < e₀)
                                  × ((x : ℝ) → a < x → x < b
                                     → Has-Sign (opposite σ) (g x)))
             → Σ (a , b) ꞉ ℚ × ℚ ,
                 (0ℚ < a) × (a < b) × (b < e₀) × Avoids p r r' a b
           θ ((a , b) , 0<a , a<b , b<e₀ , signed) =
            (a , b) , 0<a , a<b , b<e₀ , avoids a b signed

         left : (e₀ : ℚ) → e₀ < 0ℚ
              → ∃ (a , b) ꞉ ℚ × ℚ ,
                  (e₀ < a) × (a < b) × (b < 0ℚ) × Avoids p r r' a b
         left e₀ l = ∥∥-functor θ (signed-left (opposite σ) e₀ l)
          where
           θ : (Σ (a , b) ꞉ ℚ × ℚ , (e₀ < a) × (a < b) × (b < 0ℚ)
                                  × ((x : ℝ) → a < x → x < b
                                     → Has-Sign (opposite σ) (g x)))
             → Σ (a , b) ꞉ ℚ × ℚ ,
                 (e₀ < a) × (a < b) × (b < 0ℚ) × Avoids p r r' a b
           θ ((a , b) , e₀<a , a<b , b<0 , signed) =
            (a , b) , e₀<a , a<b , b<0 , avoids a b signed

         ζ : (@♭ s : ℝ) → r < s → s < r' → In-Plateau-At-Zero p q lo hi s
         ζ s c d =
          ps-is-0 , zeros (q s) (pr₁ (k s c d)) (pr₂ (k s c d)) gqs-is-0
          where
           ps-is-0 : p s ＝ 0ℝ
           ps-is-0 = stays-at-zero cem continuity p t r r' r<t t<r' pt-is-0
                      (right , left) s c d

           gqs-is-0 : g (q s) ＝ 0ℝ
           gqs-is-0 = same-height s ⁻¹ ∙ ap g ps-is-0 ∙ g-vanishes-at-zero

     γ : (q t < hi) ∔ ¬ (q t < hi) → Holds-Near (In-Plateau-At-Zero p q lo hi) t
     γ (inl l) = κ (weak-sign-below-hi C (q t) m l)
     γ (inr ν) = κ (weak-sign-above-lo C (q t)
                     (located-above (q t) lo hi (Plateau.lo<hi C) ν) m')

   U-is-co-open : Open-At-Crisp-Points cem (In-Plateau-At-Zero p q lo hi)
                   (In-Plateau-At-Zero-is-prop p q lo hi) 0ℚ 1ℚ
                   (λ t → ¬ In-Plateau-At-Zero p q lo hi t)
   U-is-co-open t _ _ ν =
    γ (cem (p t ＝ 0ℝ) ℝ-is-set)
      (cem' (q t < lo) (∈-is-prop (upper-cut-of (q t)) lo))
      (cem' (hi < q t) (∈-is-prop (lower-cut-of (q t)) hi))
    where
     W : ℝ → 𝓤₁ ̇
     W s = ¬ In-Plateau-At-Zero p q lo hi s

     from-nonzero : (σ : 𝟚) → Has-Sign σ (p t) → Holds-Near W t
     from-nonzero ₀ l = holds-near-map (λ s → p s < 0ℚ) W t
                         (λ s k u → ℚ<-irrefl 0ℚ
                                     (transport (λ (y : ℝ) → y < 0ℚ) (pr₁ u) k))
                         (upper-semicontinuity continuity p t 0ℚ l)
     from-nonzero ₁ l = holds-near-map (λ s → 0ℚ < p s) W t
                         (λ s k u → ℚ<-irrefl 0ℚ
                                     (transport (λ (y : ℝ) → 0ℚ < y) (pr₁ u) k))
                         (lower-semicontinuity continuity p t 0ℚ l)

     γ : (p t ＝ 0ℝ) ∔ ¬ (p t ＝ 0ℝ)
       → (q t < lo) ∔ ¬ (q t < lo)
       → (hi < q t) ∔ ¬ (hi < q t)
       → Holds-Near W t
     γ (inr n) _ _ = from-nonzero (pr₁ (crisp-nonzero-has-sign cem (p t) n))
                                  (pr₂ (crisp-nonzero-has-sign cem (p t) n))
     γ (inl _) (inl l) _ = holds-near-map (λ s → q s < lo) W t
                            (λ s k u → pr₁ (pr₂ u) k)
                            (upper-semicontinuity continuity q t lo l)
     γ (inl _) (inr _) (inl l) = holds-near-map (λ s → hi < q s) W t
                                  (λ s k u → pr₂ (pr₂ u) k)
                                  (lower-semicontinuity continuity q t hi l)
     γ (inl e) (inr m) (inr m') = 𝟘-elim (ν (e , m , m'))

  plateau-at-zero-persists : In-Plateau-At-Zero p q lo hi 0ℝ
                           ↔ In-Plateau-At-Zero p q lo hi 1ℝ
  plateau-at-zero-persists =
   crisp-interval-is-connected cem (In-Plateau-At-Zero p q lo hi)
    (In-Plateau-At-Zero-is-prop p q lo hi) 0ℚ 1ℚ 0<1 U-is-open U-is-co-open

\end{code}

From now on, the zeros of g lie in plateaux. If one coordinate of a
crisp path in the kernel is 0 and the other is not at one end, the
same holds at the other end.

\begin{code}

 module _ (@♭ zeros : Zeros-Lie-In-Plateaux g) where

  private
   Zero-And-Nonzero : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → 𝓤₁ ̇
   Zero-And-Nonzero p q t = (p t ＝ 0ℝ) × ¬ (q t ＝ 0ℝ)

   Zero-And-Nonzero-is-prop : (p q : ℝ → ℝ) (t : ℝ)
                            → is-prop (Zero-And-Nonzero p q t)
   Zero-And-Nonzero-is-prop p q t = ×-is-prop ℝ-is-set (negations-are-props fe)

  module _ (@♭ p q : ℝ → ℝ)
           (same-height : (t : ℝ) → g (p t) ＝ g (q t))
         where

   private
    from-plateau : (@♭ a b : ℝ)
                 → ((@♭ lo hi : ℚ) → Plateau g lo hi
                                  → In-Plateau-At-Zero p q lo hi a
                                  → In-Plateau-At-Zero p q lo hi b)
                 → Zero-And-Nonzero p q a → Zero-And-Nonzero p q b
    from-plateau a b transfer (pa-is-0 , qa-is-not-0) =
     ∥∥-rec (Zero-And-Nonzero-is-prop p q b) γ
      (zeros (q a) gqa-is-0 qa-is-not-0)
     where
      gqa-is-0 : g (q a) ＝ 0ℝ
      gqa-is-0 = same-height a ⁻¹ ∙ ap g pa-is-0 ∙ g-vanishes-at-zero

      γ : (Σ (lo , hi) ꞉ ℚ × ℚ , Plateau g lo hi × ¬ (q a < lo) × ¬ (hi < q a))
        → Zero-And-Nonzero p q b
      γ ((lo , hi) , C , m , m') =
       crisp-elim₂ ℚ-has-crisp-representatives ℚ-has-crisp-representatives
        (λ lo hi → Plateau g lo hi → ¬ (q a < lo) → ¬ (hi < q a)
                   → Zero-And-Nonzero p q b)
        κ lo hi C m m'
       where
        κ : (@♭ lo₀ hi₀ : ℚ) → Plateau g lo₀ hi₀ → ¬ (q a < lo₀) → ¬ (hi₀ < q a)
          → Zero-And-Nonzero p q b
        κ lo₀ hi₀ C₀ m₀ m₀' =
         pr₁ u₁ , plateaux-avoid-zero C₀ (q b) (pr₁ (pr₂ u₁)) (pr₂ (pr₂ u₁))
         where
          u₁ : In-Plateau-At-Zero p q lo₀ hi₀ b
          u₁ = transfer lo₀ hi₀ C₀ (pa-is-0 , m₀ , m₀')

   zero-and-nonzero-persists : Zero-And-Nonzero p q 0ℝ ↔ Zero-And-Nonzero p q 1ℝ
   zero-and-nonzero-persists =
    from-plateau 0ℝ 1ℝ
     (λ lo hi C →
       lr-implication (plateau-at-zero-persists p q same-height lo hi C)) ,
    from-plateau 1ℝ 0ℝ
     (λ lo hi C →
       rl-implication (plateau-at-zero-persists p q same-height lo hi C))

\end{code}

The invariance of h. The coordinates of a path in the kernel are
defined at top level, so that they are crisp when the path is.

\begin{code}

  first-coordinate second-coordinate : (ℝ → N cem g) → ℝ → ℝ
  first-coordinate  γ t = pr₁ (pr₁ (γ t))
  second-coordinate γ t = pr₂ (pr₁ (γ t))

  private
   δ-₁ : (@♭ x : ℝ) → δ cem (x ^♭) ＝ ₁ → x ＝ 0ℝ
   δ-₁ = crisp-test-₁ cem (λ x → x ＝ 0ℝ) (λ _ → ℝ-is-set)

   δ-₀ : (@♭ x : ℝ) → δ cem (x ^♭) ＝ ₀ → ¬ (x ＝ 0ℝ)
   δ-₀ = crisp-test-₀ cem (λ x → x ＝ 0ℝ) (λ _ → ℝ-is-set)

  zero-indicator-is-invariant : Real-Path-Invariant (N cem g) (h cem g)
  zero-indicator-is-invariant γ =
   ε (δ cem (z₀ ^♭)) (δ cem (w₀ ^♭)) (δ cem (z₁ ^♭)) (δ cem (w₁ ^♭)) refl refl
    refl refl
   where
    z₀ w₀ z₁ w₁ : ℝ
    z₀ = first-coordinate  γ 0ℝ
    w₀ = second-coordinate γ 0ℝ
    z₁ = first-coordinate  γ 1ℝ
    w₁ = second-coordinate γ 1ℝ

    I : Zero-And-Nonzero (first-coordinate γ) (second-coordinate γ) 0ℝ
      ↔ Zero-And-Nonzero (first-coordinate γ) (second-coordinate γ) 1ℝ
    I = zero-and-nonzero-persists (first-coordinate γ) (second-coordinate γ)
         (λ t → pr₂ (γ t))

    II : Zero-And-Nonzero (second-coordinate γ) (first-coordinate γ) 0ℝ
       ↔ Zero-And-Nonzero (second-coordinate γ) (first-coordinate γ) 1ℝ
    II = zero-and-nonzero-persists (second-coordinate γ) (first-coordinate γ)
          (λ t → pr₂ (γ t) ⁻¹)

    ε : (b₀ c₀ b₁ c₁ : 𝟚)
      → δ cem (z₀ ^♭) ＝ b₀ → δ cem (w₀ ^♭) ＝ c₀
      → δ cem (z₁ ^♭) ＝ b₁ → δ cem (w₁ ^♭) ＝ c₁
      → b₀ ⊕ c₀ ＝ b₁ ⊕ c₁
    ε ₀ ₀ ₀ ₀ _ _ _ _ = refl
    ε ₀ ₀ ₀ ₁ e₀ f₀ e₁ f₁ =
     𝟘-elim (δ-₀ w₀ f₀ (pr₁ (rl-implication II (δ-₁ w₁ f₁ , δ-₀ z₁ e₁))))
    ε ₀ ₀ ₁ ₀ e₀ f₀ e₁ f₁ =
     𝟘-elim (δ-₀ z₀ e₀ (pr₁ (rl-implication I (δ-₁ z₁ e₁ , δ-₀ w₁ f₁))))
    ε ₀ ₀ ₁ ₁ _ _ _ _ = refl
    ε ₀ ₁ ₀ ₀ e₀ f₀ e₁ f₁ =
     𝟘-elim (δ-₀ w₁ f₁ (pr₁ (lr-implication II (δ-₁ w₀ f₀ , δ-₀ z₀ e₀))))
    ε ₀ ₁ ₀ ₁ _ _ _ _ = refl
    ε ₀ ₁ ₁ ₀ _ _ _ _ = refl
    ε ₀ ₁ ₁ ₁ e₀ f₀ e₁ f₁ =
     𝟘-elim (pr₂ (lr-implication II (δ-₁ w₀ f₀ , δ-₀ z₀ e₀)) (δ-₁ z₁ e₁))
    ε ₁ ₀ ₀ ₀ e₀ f₀ e₁ f₁ =
     𝟘-elim (δ-₀ z₁ e₁ (pr₁ (lr-implication I (δ-₁ z₀ e₀ , δ-₀ w₀ f₀))))
    ε ₁ ₀ ₀ ₁ _ _ _ _ = refl
    ε ₁ ₀ ₁ ₀ _ _ _ _ = refl
    ε ₁ ₀ ₁ ₁ e₀ f₀ e₁ f₁ =
     𝟘-elim (pr₂ (lr-implication I (δ-₁ z₀ e₀ , δ-₀ w₀ f₀)) (δ-₁ w₁ f₁))
    ε ₁ ₁ ₀ ₀ _ _ _ _ = refl
    ε ₁ ₁ ₀ ₁ e₀ f₀ e₁ f₁ =
     𝟘-elim (pr₂ (rl-implication II (δ-₁ w₁ f₁ , δ-₀ z₁ e₁)) (δ-₁ z₀ e₀))
    ε ₁ ₁ ₁ ₀ e₀ f₀ e₁ f₁ =
     𝟘-elim (pr₂ (rl-implication I (δ-₁ z₁ e₁ , δ-₀ w₁ f₁)) (δ-₁ w₀ f₀))
    ε ₁ ₁ ₁ ₁ _ _ _ _ = refl

\end{code}
