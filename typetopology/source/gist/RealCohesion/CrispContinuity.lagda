Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026; prose corrected 13 November 2026, after
the final audits. See the AI disclosure in gist.RealCohesion.index.

Continuity of crisp real functions at crisp points, without Axiom T.

Shulman proves that crisp functions ℝ → ℝ are ε-δ continuous at crisp
points [1, Theorem 11.5]. His proof uses Axioms R♭ and T, and crisp
excluded middle through his Theorem 8.32. Fable's note [2] removes
Axiom T. Its key step is sequential continuity (Proposition A.1),
which we obtain from interval hitting
(gist.RealCohesion.IntervalHitting), so from Axiom R♭ alone, instead
of from Lemma S.

Assuming crisp excluded middle and that every map ℝ → Q is constant,
which follows from Axiom R♭ by
gist.RealCohesion.FiniteChainDiscreteness, we prove the following.

 * Crisp rational approximations [1, Theorem 6.32]. A crisp real
   number s is the limit of the sequence of rationals whose j-th term
   is the first rational within ρ j of s, in the enumeration of
   gist.RealCohesion.RationalEnumeration. Whether a rational is within
   ρ j of s is a crisp proposition, which crisp excluded middle
   decides, so no choice is involved.

 * Sequential continuity [2, Proposition A.1], [3, Proposition 3.2],
   for n = 1. If f, p and the sequence x are crisp, and x k is within
   ρ k of p, then f (x k) is eventually in every rational interval
   around f p.

 * Continuity at crisp points. The interface Crisp-Real-Continuity of
   gist.RealCohesion.CrispRealAnalysis, an assumption of the results
   for nLab problem 1, is a theorem: for crisp f and t and rationals
   u < f t < v, there is a rational interval around t on whose crisp
   points u < f < v. This is [2, Theorem A.2] for n = 1 with y crisp,
   that is, ε-δ continuity in the discrete world, the notion of
   [1, Corollary 11.6].

The proof of continuity follows [2]. Choose crisp rationals with
u < u₁ < f t < v₁ < v. If the conclusion fails, then by crisp excluded
middle every rational interval around t contains a crisp s with
f s < u₁ or v₁ < f s. Interval hitting at s, along the rational
approximations of s, gives a rational point of the interval with the
same property. Least-witness search then gives a sequence of such
rational points converging to t, and interval hitting at t
contradicts it.

[2, Theorem A.2] in full also covers the points of the interval that
are not crisp. Its proof uses Shulman's Corollary 8.16, that a crisp
type without crisp points is empty, which rests on ♭ commuting with
propositional truncation [1, Corollary 6.7]. That needs crisp
induction on the truncation, which TypeTopology's truncations, not
being inductive types, did not provide when this module was written,
for Agda 2.8. So this module stays with crisp points. The points that
are not crisp are reached later by other means:
gist.RealCohesion.CrispFunctionsEverywhere uses rational detection,
and gist.RealCohesion.CrispFunctionsAreContinuous proves the
continuity from Axiom R♭ alone. With the native ♯ of Agda 2.9.0, a
crisp element of a truncation gives an element of the truncation of
♭ (gist.Orbifolds.CrispTruncation), and Corollary 8.16 is proved
under Axiom C1 (gist.RealCohesion.BoundaryRetractionFromC1); this
module does not use them.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] Fable. Shulman's stated questions: three updates, Part A.
    Working note, 10 November 2026, audited by GPT-6 Astra.
    references/F18-shulman-three-updates.md

[3] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revised 10 November 2026, §3.
    references/C02-write-up-2026-11-10.tex

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispContinuity
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Naturals.Order hiding (max)
open import Naturals.ExitTruncation
open import NotionsOfDecidability.Decidable
 using (×-preserves-decidability ; ¬-preserves-decidability)
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalArithmetic using (<-move-left)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt
 using (cuts-are-ordered ; not-below-and-above)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; ℝ<ℚ-is-prop)
open import gist.RealCohesion.RealLimits fe pe pt
 using (ρ ; ρ-is-positive ; ρ-halves ; ρ-antitone ; within ; within-trans ;
        within-weaken ; rational-approximations-exist)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.IntervalHitting fe pe pt
 using (interval-hitting ; interval-hitting₂)
open import gist.RealCohesion.RationalEnumeration pt
 using (rational-witness ; rational-witness-property)
open import gist.RealCohesion.CrispRationals
 using (ℕ-has-crisp-representatives ; ℚ-has-crisp-representatives ;
        ×-has-crisp-representatives ; crisp-elim ; crisp-elim₂ ; decide-at ;
        decide-at-rationals)
open import gist.RealCohesion.CrispDecisions using (Crisp-EM-lower)
open import gist.RealCohesion.CrispRealAnalysis fe pe pt
 using (Holds-Near ; Crisp-Real-Continuity ; crisp-rational-between)

open PropositionalTruncation pt
open exit-truncations pt

\end{code}

Decisions. The order of the rationals is decidable, and crisp excluded
middle decides a crisp family of propositions on ℕ at every natural
number, crisp or not: decide-at of gist.RealCohesion.CrispRationals
for ℕ.

\begin{code}

ℚ<-decide : (p q : ℚ) → is-decidable (p < q)
ℚ<-decide p q = γ (ℚ-trichotomous p q)
 where
  γ : (p < q) ∔ (p ＝ q) ∔ (q < p) → is-decidable (p < q)
  γ (inl l)       = inl l
  γ (inr (inl e)) = inr (λ l → ℚ<-irrefl q (transport (_< q) e l))
  γ (inr (inr m)) = inr (λ l → ℚ<-irrefl p (ℚ<-trans p q p l m))

decide-at-naturals : {@♭ 𝓦 : Universe}
                   → (@♭ cem : Crisp-EM 𝓦)
                   → (@♭ P : ℕ → 𝓦 ̇ )
                   → (@♭ P-is-prop : (n : ℕ) → is-prop (P n))
                   → (n : ℕ) → is-decidable (P n)
decide-at-naturals cem P P-is-prop =
 decide-at ℕ-has-crisp-representatives cem P P-is-prop

\end{code}

Rational approximation. A rational q approximates s at stage j if s
lies strictly between q - ρ j and q + ρ j. Such rationals exist, and
then ιₐ q is within ρ j of s.

\begin{code}

Approximates : ℝ → ℕ → ℚ → 𝓤₀ ̇
Approximates s j q = ((q ℚ- ρ j) < s) × (s < (q ℚ+ ρ j))

Approximates-is-prop : (s : ℝ) (j : ℕ) (q : ℚ) → is-prop (Approximates s j q)
Approximates-is-prop s j q =
 ×-is-prop (ℚ<ℝ-is-prop (q ℚ- ρ j) s) (ℝ<ℚ-is-prop s (q ℚ+ ρ j))

approximations-exist : (s : ℝ) (j : ℕ) → ∃ q ꞉ ℚ , Approximates s j q
approximations-exist s j =
 rational-approximations-exist s (ρ j) (ρ-is-positive j)

approximation-is-within : (s : ℝ) (j : ℕ) (q : ℚ)
                        → Approximates s j q → within (ρ j) (ιₐ q) s
approximation-is-within s j q (l , m) = I , II
 where
  I : (p : ℚ) → p < ιₐ q → (p ℚ- ρ j) < s
  I p o = use-rounded-real-L s (p ℚ- ρ j) (q ℚ- ρ j)
           (ℚ<-addition-preserves-order p q (ℚ- ρ j) (ιₐ-lower⁻¹ p q o)) l

  II : (p : ℚ) → p < s → (p ℚ- ρ j) < ιₐ q
  II p o = ιₐ-lower (p ℚ- ρ j) q
            (<-move-left p q (ρ j) (cuts-are-ordered s p (q ℚ+ ρ j) o m))

within-of-close-rationals : (ε c q : ℚ)
                          → c ℚ- ε < q → q < c ℚ+ ε → within ε (ιₐ q) (ιₐ c)
within-of-close-rationals ε c q l m = I , II
 where
  I : (p : ℚ) → p < ιₐ q → (p ℚ- ε) < ιₐ c
  I p o = ιₐ-lower (p ℚ- ε) c
           (<-move-left p c ε (ℚ<-trans p q (c ℚ+ ε) (ιₐ-lower⁻¹ p q o) m))

  II : (p : ℚ) → p < ιₐ c → (p ℚ- ε) < ιₐ q
  II p o = ιₐ-lower (p ℚ- ε) q
            (ℚ<-trans (p ℚ- ε) (c ℚ- ε) q
              (ℚ<-addition-preserves-order p c (ℚ- ε) (ιₐ-lower⁻¹ p c o)) l)

\end{code}

The crisp propositions to which we apply crisp excluded middle. They
are top-level definitions so that, applied to crisp arguments, they
are crisp.

\begin{code}

Close : (ℝ → ℝ) → (ℕ → ℝ) → ℚ → ℚ → ℕ → 𝓤₀ ̇
Close f x u v k = (u < f (x k)) × (f (x k) < v)

Close-is-prop : (f : ℝ → ℝ) (x : ℕ → ℝ) (u v : ℚ) (k : ℕ)
              → is-prop (Close f x u v k)
Close-is-prop f x u v k =
 ×-is-prop (ℚ<ℝ-is-prop u (f (x k))) (ℝ<ℚ-is-prop (f (x k)) v)

Eventually-Close : (ℝ → ℝ) → (ℕ → ℝ) → ℚ → ℚ → 𝓤₀ ̇
Eventually-Close f x u v = ∃ N ꞉ ℕ , ((k : ℕ) → N ≤ k → Close f x u v k)

Window : (ℝ → ℝ) → ℚ → ℚ → ℝ → 𝓤₀ ̇
Window f u v s = (u < f s) × (f s < v)

Window-is-prop : (f : ℝ → ℝ) (u v : ℚ) (s : ℝ) → is-prop (Window f u v s)
Window-is-prop f u v s = ×-is-prop (ℚ<ℝ-is-prop u (f s)) (ℝ<ℚ-is-prop (f s) v)

Bad : (ℝ → ℝ) → ℚ → ℚ → ℚ → 𝓤₀ ̇
Bad f u₁ v₁ q = (f (ιₐ q) < u₁) ∨ (v₁ < f (ιₐ q))

Crisp-Bad-Point : (ℝ → ℝ) → ℚ → ℚ → ℚ → ℚ → 𝓤₁ ̇
Crisp-Bad-Point f u v r r' =
 ∃ s ꞉ ♭ ℝ , (r < ♭-counit s) × (♭-counit s < r') × ¬ Window f u v (♭-counit s)

\end{code}

From now on we assume crisp excluded middle.

\begin{code}

module _ (@♭ cem : Crisp-EM 𝓤₁) where

 cem₀ : Crisp-EM 𝓤₀
 cem₀ = Crisp-EM-lower {𝓤₀} {𝓤₁} cem

 decide-approximates : (@♭ s : ℝ) (j : ℕ) (q : ℚ)
                     → is-decidable (Approximates s j q)
 decide-approximates s j q =
  decide-at (×-has-crisp-representatives ℕ-has-crisp-representatives
              ℚ-has-crisp-representatives)
   cem₀ (λ p → Approximates s (pr₁ p) (pr₂ p))
   (λ p → Approximates-is-prop s (pr₁ p) (pr₂ p)) (j , q)

 rational-approximation : (@♭ s : ℝ) → ℕ → ℚ
 rational-approximation s j = rational-witness (Approximates s j)
                               (decide-approximates s j)
                                (approximations-exist s j)

 rational-approximation-approximates
  : (@♭ s : ℝ) (j : ℕ) → Approximates s j (rational-approximation s j)
 rational-approximation-approximates s j =
  rational-witness-property (Approximates s j) (decide-approximates s j)
   (approximations-exist s j)

 rational-approximation-converges
  : (@♭ s : ℝ) (j : ℕ) → within (ρ j) (ιₐ (rational-approximation s j)) s
 rational-approximation-converges s j =
  approximation-is-within s j (rational-approximation s j)
   (rational-approximation-approximates s j)

 decide-close : (@♭ f : ℝ → ℝ) (@♭ x : ℕ → ℝ) (@♭ u v : ℚ) (k : ℕ)
              → is-decidable (Close f x u v k)
 decide-close f x u v =
  decide-at-naturals cem₀ (Close f x u v) (Close-is-prop f x u v)

 failures-are-late : (@♭ f : ℝ → ℝ) (@♭ x : ℕ → ℝ) (@♭ u v : ℚ)
                   → ¬ Eventually-Close f x u v
                   → (j : ℕ) → ∃ k ꞉ ℕ , (j ≤ k) × ¬ Close f x u v k
 failures-are-late f x u v n =
  crisp-elim ℕ-has-crisp-representatives
   (λ j → ∃ k ꞉ ℕ , (j ≤ k) × ¬ Close f x u v k) γ
  where
   γ : (@♭ j : ℕ) → ∃ k ꞉ ℕ , (j ≤ k) × ¬ Close f x u v k
   γ j = Cases (cem₀ (∃ k ꞉ ℕ , (j ≤ k) × ¬ Close f x u v k) ∃-is-prop)
          id
          (λ m → 𝟘-elim (n ∣ j , (λ k l → δ m k l) ∣))
    where
     δ : ¬ (∃ k ꞉ ℕ , (j ≤ k) × ¬ Close f x u v k)
       → (k : ℕ) → j ≤ k → Close f x u v k
     δ m k l =
      Cases (decide-close f x u v k) id (λ c → 𝟘-elim (m ∣ k , l , c ∣))

\end{code}

From now on we also assume that every map ℝ → Q is constant.
Sequential continuity.

\begin{code}

 module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

  sequential-continuity-for-crisp-bounds
   : (@♭ f : ℝ → ℝ) (@♭ p : ℝ) (@♭ x : ℕ → ℝ)
   → ((k : ℕ) → within (ρ k) (x k) p)
   → (@♭ u v : ℚ) → u < f p → f p < v
   → Eventually-Close f x u v
  sequential-continuity-for-crisp-bounds f p x c u v l m =
   Cases (cem₀ (Eventually-Close f x u v) ∃-is-prop) id (λ n → 𝟘-elim (γ n))
   where
    γ : ¬ Eventually-Close f x u v → 𝟘
    γ n = ∥∥-rec 𝟘-is-prop δ (interval-hitting ν f p y y-converges u v l m)
     where
      selected : (j : ℕ) → Σ k ꞉ ℕ , (j ≤ k) × ¬ Close f x u v k
      selected j = exit-truncation (λ k → (j ≤ k) × ¬ Close f x u v k)
                    (λ k → ×-preserves-decidability (≤-decidable j k)
                             (¬-preserves-decidability
                               (decide-close f x u v k)))
                    (failures-are-late f x u v n j)

      y : ℕ → ℝ
      y j = x (pr₁ (selected j))

      y-converges : (j : ℕ) → within (ρ j) (y j) p
      y-converges j = within-weaken (ρ (pr₁ (selected j))) (ρ j) (y j) p
                       (ρ-antitone j (pr₁ (selected j))
                         (pr₁ (pr₂ (selected j))))
                       (c (pr₁ (selected j)))

      δ : (Σ j ꞉ ℕ , (u < f (y j)) × (f (y j) < v)) → 𝟘
      δ (j , o) = pr₂ (pr₂ (selected j)) o

  crisp-sequential-continuity
   : (@♭ f : ℝ → ℝ) (@♭ p : ℝ) (@♭ x : ℕ → ℝ)
   → ((k : ℕ) → within (ρ k) (x k) p)
   → (u v : ℚ) → u < f p → f p < v
   → ∃ N ꞉ ℕ , ((k : ℕ) → N ≤ k → (u < f (x k)) × (f (x k) < v))
  crisp-sequential-continuity f p x c =
   crisp-elim₂ ℚ-has-crisp-representatives ℚ-has-crisp-representatives
    (λ u v → u < f p → f p < v → Eventually-Close f x u v)
    (sequential-continuity-for-crisp-bounds f p x c)

\end{code}

Continuity at crisp points. First, if continuity fails at t for the
window (u , v), every rational interval around t with crisp endpoints
contains a crisp point outside the window.

\begin{code}

  crisp-bad-points
   : (@♭ f : ℝ → ℝ) (@♭ t : ℝ) (@♭ u v : ℚ)
   → ¬ Holds-Near (Window f u v) t
   → (@♭ r r' : ℚ) → r < t → t < r'
   → Crisp-Bad-Point f u v r r'
  crisp-bad-points f t u v n r r' a b =
   Cases (cem (Crisp-Bad-Point f u v r r') ∃-is-prop) id
    (λ m → 𝟘-elim (n ∣ (r , r') , a , b , good m ∣))
   where
    good : ¬ Crisp-Bad-Point f u v r r' → (@♭ s : ℝ) → r < s → s < r'
         → Window f u v s
    good m s c d = Cases (cem₀ (Window f u v s) (Window-is-prop f u v s)) id
                    (λ w → 𝟘-elim (m ∣ (s ^♭) , c , d , w ∣))

\end{code}

Second, a crisp point outside the window (u , v), in a rational
interval, gives a rational point of the interval outside the narrower
window (u₁ , v₁), by interval hitting at the crisp point along its
rational approximations.

\begin{code}

  rational-bad-point
   : (@♭ f : ℝ → ℝ) (@♭ u v u₁ v₁ : ℚ)
   → u < u₁ → v₁ < v
   → (@♭ r r' : ℚ)
   → Crisp-Bad-Point f u v r r'
   → ∃ q ꞉ ℚ , ((r < q) × (q < r')) × Bad f u₁ v₁ q
  rational-bad-point f u v u₁ v₁ a b r r' = ∥∥-rec ∃-is-prop γ
   where
    γ : (Σ s ꞉ ♭ ℝ ,
          (r < ♭-counit s) × (♭-counit s < r') × ¬ Window f u v (♭-counit s))
      → ∃ q ꞉ ℚ , ((r < q) × (q < r')) × Bad f u₁ v₁ q
    γ ((s ^♭) , c , d , w) = ∥∥-rec ∃-is-prop δ (ℝ-locatedness (f s) u u₁ a)
     where
      q : ℕ → ℚ
      q = rational-approximation s

      z : ℕ → ℝ
      z j = ιₐ (q j)

      z-converges : (j : ℕ) → within (ρ j) (z j) s
      z-converges = rational-approximation-converges s

      Goal : 𝓤₀ ̇
      Goal = Σ q' ꞉ ℚ , ((r < q') × (q' < r')) × Bad f u₁ v₁ q'

      Hit : ℚ → ℚ → 𝓤₀ ̇
      Hit L U =
       Σ j ꞉ ℕ , ((L < f (z j)) × (f (z j) < U)) × ((r < z j) × (z j < r'))

      in-interval : (j : ℕ) → (r < z j) × (z j < r') → (r < q j) × (q j < r')
      in-interval j (o , o') = ιₐ-lower⁻¹ r (q j) o , ιₐ-upper⁻¹ (q j) r' o'

      hit-below : (L : ℚ) → Hit L u₁ → Goal
      hit-below L (j , (_ , o) , i) = q j , in-interval j i , ∣ inl o ∣

      hit-above : (U : ℚ) → Hit v₁ U → Goal
      hit-above U (j , (o , _) , i) = q j , in-interval j i , ∣ inr o ∣

      hitting : (L U : ℚ) → L < f s → f s < U → ∥ Hit L U ∥
      hitting L U l m =
       interval-hitting₂ ν f id s z z-converges L U r r' l m c d

      δ : (u < f s) ∔ (f s < u₁) → ∥ Goal ∥
      δ (inr e) = ∥∥-rec ∃-is-prop ε (inhabited-from-real-L (f s))
       where
        ε : (Σ L ꞉ ℚ , L < f s) → ∥ Goal ∥
        ε (L , L<fs) = ∥∥-functor (hit-below L) (hitting L u₁ L<fs e)
      δ (inl e) = ∥∥-rec ∃-is-prop ε (ℝ-locatedness (f s) v₁ v b)
       where
        ε : (v₁ < f s) ∔ (f s < v) → ∥ Goal ∥
        ε (inl e') = ∥∥-rec ∃-is-prop ζ (inhabited-from-real-R (f s))
         where
          ζ : (Σ U ꞉ ℚ , f s < U) → ∥ Goal ∥
          ζ (U , fs<U) = ∥∥-functor (hit-above U) (hitting v₁ U e' fs<U)
        ε (inr e') = 𝟘-elim (w (e , e'))

\end{code}

Third, if continuity failed at t, least-witness search would give a
sequence of rational points converging to t outside the window
(u₁ , v₁), which interval hitting at t rules out.

\begin{code}

  no-discontinuity
   : (@♭ f : ℝ → ℝ) (@♭ t : ℝ) (@♭ u v u₁ v₁ : ℚ)
   → u < u₁ → v₁ < v → u₁ < f t → f t < v₁
   → ¬¬ Holds-Near (Window f u v) t
  no-discontinuity f t u v u₁ v₁ a b l m n =
   ∥∥-rec 𝟘-is-prop δ (interval-hitting ν f t z z-converges u₁ v₁ l m)
   where
    c : ℕ → ℚ
    c k = rational-approximation t (succ k)

    c-approximates : (k : ℕ) → Approximates t (succ k) (c k)
    c-approximates k = rational-approximation-approximates t (succ k)

    P : ℕ → ℚ → 𝓤₀ ̇
    P k q = ((c k ℚ- ρ (succ k) < q) × (q < c k ℚ+ ρ (succ k))) × Bad f u₁ v₁ q

    decide-P : (k : ℕ) (q : ℚ) → is-decidable (P k q)
    decide-P k q =
     ×-preserves-decidability
      (×-preserves-decidability
        (ℚ<-decide (c k ℚ- ρ (succ k)) q) (ℚ<-decide q (c k ℚ+ ρ (succ k))))
      (decide-at-rationals cem₀ (Bad f u₁ v₁) (λ _ → ∨-is-prop) q)

    bad-points-exist : (k : ℕ) → ∃ q ꞉ ℚ , P k q
    bad-points-exist k =
     crisp-elim₂ ℚ-has-crisp-representatives ℚ-has-crisp-representatives
      (λ x y → x < t → t < y → ∃ q ꞉ ℚ , ((x < q) × (q < y)) × Bad f u₁ v₁ q)
      (λ r r' o o' → rational-bad-point f u v u₁ v₁ a b r r'
                      (crisp-bad-points f t u v n r r' o o'))
      (c k ℚ- ρ (succ k)) (c k ℚ+ ρ (succ k))
      (pr₁ (c-approximates k)) (pr₂ (c-approximates k))

    q : ℕ → ℚ
    q k = rational-witness (P k) (decide-P k) (bad-points-exist k)

    q-is-bad : (k : ℕ) → P k (q k)
    q-is-bad k =
     rational-witness-property (P k) (decide-P k) (bad-points-exist k)

    z : ℕ → ℝ
    z k = ιₐ (q k)

    z-converges : (k : ℕ) → within (ρ k) (z k) t
    z-converges k =
     transport (λ ε → within ε (z k) t) (ρ-halves k)
      (within-trans (ρ (succ k)) (ρ (succ k)) (z k) (ιₐ (c k)) t
        (within-of-close-rationals (ρ (succ k)) (c k) (q k)
          (pr₁ (pr₁ (q-is-bad k))) (pr₂ (pr₁ (q-is-bad k))))
        (approximation-is-within t (succ k) (c k) (c-approximates k)))

    δ : (Σ k ꞉ ℕ , (u₁ < f (z k)) × (f (z k) < v₁)) → 𝟘
    δ (k , o , o') = ∥∥-rec 𝟘-is-prop ε (pr₂ (q-is-bad k))
     where
      ε : (f (z k) < u₁) ∔ (v₁ < f (z k)) → 𝟘
      ε (inl p) = not-below-and-above (f (z k)) u₁ o p
      ε (inr p) = not-below-and-above (f (z k)) v₁ p o'

\end{code}

Continuity at crisp points, first for crisp bounds and then in the
form Crisp-Real-Continuity.

\begin{code}

  continuity-for-crisp-bounds
   : (@♭ f : ℝ → ℝ) (@♭ t : ℝ) (@♭ u v : ℚ)
   → u < f t → f t < v
   → Holds-Near (Window f u v) t
  continuity-for-crisp-bounds f t u v l m =
   Cases (cem (Holds-Near (Window f u v) t) ∃-is-prop) id
    (λ n → 𝟘-elim (∥∥-rec 𝟘-is-prop (γ n) (rounded-left-d (f t) u l)))
   where
    γ : ¬ Holds-Near (Window f u v) t → (Σ u₂ ꞉ ℚ , (u < u₂) × (u₂ < f t)) → 𝟘
    γ n (u₂ , a₂ , b₂) =
     ∥∥-rec 𝟘-is-prop δ
      (rounded-right-b (upper-cut-of (f t)) (rounded-from-real-R (f t)) v m)
     where
      δ : (Σ v₂ ꞉ ℚ , (v₂ < v) × (f t < v₂)) → 𝟘
      δ (v₂ , a₃ , b₃) =
       ε (crisp-rational-between u u₂ a₂) (crisp-rational-between v₂ v a₃)
       where
        ε : (Σ e ꞉ ♭ ℚ , (u < ♭-counit e) × (♭-counit e < u₂))
          → (Σ e ꞉ ♭ ℚ , (v₂ < ♭-counit e) × (♭-counit e < v))
          → 𝟘
        ε ((u₁ ^♭) , a₁ , b₁) ((v₁ ^♭) , a₁' , b₁') =
         no-discontinuity f t u v u₁ v₁ a₁ b₁'
          (use-rounded-real-L (f t) u₁ u₂ b₁ b₂)
          (use-rounded-real-R (f t) v₂ v₁ a₁' b₃)
          n

  crisp-real-continuity : Crisp-Real-Continuity
  crisp-real-continuity f t =
   crisp-elim₂ ℚ-has-crisp-representatives ℚ-has-crisp-representatives
    (λ u v → u < f t → f t < v → Holds-Near (λ s → (u < f s) × (f s < v)) t)
    (continuity-for-crisp-bounds f t)

\end{code}
