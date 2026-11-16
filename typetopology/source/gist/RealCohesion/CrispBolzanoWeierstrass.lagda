Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026; its bisection moved to
gist.RealCohesion.CrispBisection 12 November 2026. See the AI disclosure
in gist.RealCohesion.index.

Bolzano–Weierstrass for crisp sequences of rational points of the
cube [-1,1]ⁿ.

Exact statement served: Lemma 3.6 of the write-up [1]. Assume Axiom
LEM. Let n be a crisp natural number, C = [-1,1]ⁿ, and (q k) a crisp
sequence of rational points of C. Then there are a crisp point p of C
and a crisp sequence of indices k 0 < k 1 < ⋯ such that
|q (k i) - p| ≤ 2⁻ⁱ for all i.

Relation: Lemma-3-6 below is this statement with the supremum norm in
place of the Euclidean norm of §3 of the write-up. The bound is written
coordinate by coordinate as two inequalities, as in
gist.RealCohesion.BrouwerStatements. A bound 2⁻ⁱ in the supremum norm
gives the bound 2⁻ⁱ in the Euclidean norm after passing to the
subsequence i ↦ k (i + c) with 2ᶜ ≥ √n; that form cannot be stated
before the library has the Euclidean norm (Part E of the addendum [2]).
The write-up's proof of Corollary 3.7 converts to the supremum norm
anyway. Axiom LEM is used only as crisp excluded middle for
propositions in 𝓤₀, and the crispness of the conclusion is expressed
with ♭. The addendum [2, §5.5] proposed indices with j ≤ k j in place
of strictly increasing ones; that form follows (indices-grow).

The proof is the write-up's, which is Claude Fable 5.2's and which GPT-6
Astra audited on paper on 11 November 2026 [2]: subdivide the cube
repeatedly into 2ⁿ subcubes of half the side, keeping at each step a
subcube that contains q k for arbitrarily large k. The nested cubes
determine p, and k i is the least index after k (i - 1) with q (k i) in
the cube of step i + 1. The addendum proposed instead to treat one
coordinate at a time, by induction on the crisp n, which needs crisp
induction on ℕ. The subdivision needs none, and no ♯: every decision
concerns a box, a cube with a rational corner and a rational side. A box
is a finite datum with crisp representatives
(gist.RealCohesion.CrispRationals), so crisp excluded middle decides at
every box whether the sequence visits it arbitrarily late, crisp or not
(decide-at). If a box is visited arbitrarily late, so is one of its 2ⁿ
subcubes; otherwise the largest of their last-visit bounds would bound
the visits to the box (pigeonhole). Such a subcube is found by
exhaustive search over the 2ⁿ choices (TypeTopology's compactness of
finite products), and every index is the least witness of a decidable
predicate (Naturals.ExitTruncation), so no choice principle is used.

The subdivision, the search and the pigeonhole argument are now
gist.RealCohesion.CrispBisection, for a general family of propositions
on boxes in place of the visits; this module is its instance, and
re-exports it, so that its names keep their types.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, seventh revision of 11 November 2026,
    Lemma 3.6 and the proof of Corollary 3.7.
    references/C03-write-up-2026-11-11-seventh.tex
    references/C03a-write-up-seventh-README.txt

[2] Formalization blueprint, addendum: Theorem 7.10, Corollary 3.7,
    Theorem 4.3 and Theorem 8.32, revision 4, §1a, §5.1 and §5.5.
    Claude Fable 5.2, 11 November 2026.
    references/F14-brouwer-addendum-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.CrispBolzanoWeierstrass
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Fin.Topology
 using (Fin-Π-Compact ; finitely-indexed-product-compact)
open import Fin.Type
open import Naturals.ExitTruncation
open import Naturals.Order
open import NotionsOfDecidability.Decidable
 using (×-preserves-decidability ; ¬-preserves-decidability)
open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Addition
open import Rationals.Multiplication using (ℚ-mult-left-id)
open import Rationals.Order
open import Rationals.Type
open import Rationals.Limits fe pe pt using (⟨1/2⟩^_)
open import TypeTopology.CompactTypes
 using (is-Compact ; compact-types-are-Compact ; 𝟚-is-compact)
open import UF.Base
open import UF.Subsingletons-FunExt using (Π-is-prop)
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.BrouwerStatements fe pe pt
 using (ℝ^ ; in-cube ; rational-point ; _is-within-2⁻_of_)
open import gist.RealCohesion.CrispBisection fe pe pt public
open import gist.RealCohesion.CrispRationals
open import gist.RealCohesion.NestedIntervals fe pe pt
open import gist.RealCohesion.RationalArithmetic
open import gist.RealCohesion.RationalArithmetic
 using (two ; two-is-nonneg ; minus-one-plus-two) public
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealLimits fe pe pt
 using (ρ-becomes-small ; within ; within-in-interval)
open import gist.RealCohesion.RealOrder fe pe pt using (embedding-reflects-≤)
open import gist.RealCohesion.SequentialHitting fe pe pt
 using (starter-bounds-from-within)

open PropositionalTruncation pt
open exit-truncations pt

\end{code}
From now on, crisp excluded middle and a crisp sequence q of rational
points. The bisection of gist.RealCohesion.CrispBisection, for the
family Visited and the box [-1,1]ⁿ: Visited is crisp, a visit after
index K' is a visit after every K ≤ K', and a visit to a box is a visit
to one of its subcubes.

\begin{code}

module _ (@♭ cem : Crisp-EM 𝓤₀)
         {@♭ n : ℕ}
         (@♭ q : ℕ → Fin n → ℚ)
       where

 Visited : Box n → ℕ → 𝓤₀ ̇
 Visited B K = ∃ k ꞉ ℕ , (K ≤ k) × (q k is-in B)

 open bisection cem Visited (λ B K → ∃-is-prop) (λ _ → -1ℚ) public
  renaming (Often to Often-Visited ;
            decide-V to decide-visited ;
            decide-often to decide-often-visited ;
            decide-eventually-not to decide-eventually-unvisited ;
            last to last-visit)

 visits-are-antitone : (B : Box n) (K K' : ℕ) → K ≤ K' → Visited B K'
                     → Visited B K
 visits-are-antitone B K K' l = ∥∥-functor γ
  where
   γ : (Σ k ꞉ ℕ , (K' ≤ k) × (q k is-in B)) → Σ k ꞉ ℕ , (K ≤ k) × (q k is-in B)
   γ (k , m , r) = k , ≤-trans K K' k l m , r

 visits-are-in-subcubes
  : (B : Box n) (K : ℕ) → Visited B K
  → ∃ c ꞉ (Fin n → 𝟚) , Visited (subcube c B) K
 visits-are-in-subcubes B K = ∥∥-functor γ
  where
   γ : (Σ k ꞉ ℕ , (K ≤ k) × (q k is-in B))
     → Σ c ꞉ (Fin n → 𝟚) , Visited (subcube c B) K
   γ (k , l , m) =
    subcube-containing B (q k) , ∣ k , l , subcube-contains B (q k) m ∣

 open splitting visits-are-antitone visits-are-in-subcubes public
  renaming (next-is-often to next-is-often-visited)

\end{code}

From now on q is a crisp sequence of points of the cube. The indices
k i, and the bounds.

\begin{code}

 module _ (@♭ q-in-cube : (k : ℕ) → in-cube (rational-point (q k))) where

  in-the-start : (k : ℕ) → q k is-in start
  in-the-start k i =
   embedding-reflects-≤ -1ℚ (q k i) (pr₁ (q-in-cube k i)) ,
   transport (q k i ≤_) (minus-one-plus-two ⁻¹)
    (embedding-reflects-≤ (q k i) 1ℚ (pr₂ (q-in-cube k i)))

  stages-are-often-visited : (j : ℕ) → Often-Visited (stage j)
  stages-are-often-visited =
   stages-are-often (λ K → ∣ K , ≤-refl K , in-the-start K ∣)

  visit : (j K : ℕ) → Σ k ꞉ ℕ , (K ≤ k) × (q k is-in stage j)
  visit j K = exit-truncation (λ k → (K ≤ k) × (q k is-in stage j))
               (λ k → ×-preserves-decidability (≤-decidable K k)
                        (being-in-is-decidable (q k) (stage j)))
               (stages-are-often-visited j K)

  indices : ℕ → ℕ
  indices 0        = pr₁ (visit 1 0)
  indices (succ j) = pr₁ (visit (succ (succ j)) (succ (indices j)))

  indices-increase : (j : ℕ) → indices j < indices (succ j)
  indices-increase j = pr₁ (pr₂ (visit (succ (succ j)) (succ (indices j))))

  indices-grow : (j : ℕ) → j ≤ indices j
  indices-grow 0        = zero-least (indices 0)
  indices-grow (succ j) = ≤-trans (succ j) (succ (indices j)) (indices (succ j))
                           (indices-grow j) (indices-increase j)

  indices-are-in-stages : (j : ℕ) → q (indices j) is-in stage (succ j)
  indices-are-in-stages 0        = pr₂ (pr₂ (visit 1 0))
  indices-are-in-stages (succ j) =
   pr₂ (pr₂ (visit (succ (succ j)) (succ (indices j))))

  limit-point-is-in-cube : in-cube limit-point
  limit-point-is-in-cube i =
   (λ p l → below-the-limit (coordinate-intervals i) 0 p l) ,
   (λ p l → transport (p <_) minus-one-plus-two
             (below-the-limit-gives-below-right (coordinate-intervals i) 0 p l))

  indices-converge : (j : ℕ)
                   → rational-point (q (indices j)) is-within-2⁻ j
                      of limit-point
  indices-converge j i =
   starter-bounds-from-within j (ι (q (indices j) i)) (limit-point i) w
   where
    l r : ℚ
    l = corner (succ j) i
    r = l + side (succ j)

    m : q (indices j) is-in stage (succ j)
    m = indices-are-in-stages j

    w : within (⟨1/2⟩^ j) (ι (q (indices j) i)) (limit-point i)
    w = within-in-interval (⟨1/2⟩^ j) l r (ι (q (indices j) i)) (limit-point i)
         (transport (λ - → r ≤ l + -) (side-of-next-stage j) (ℚ≤-refl r))
         (λ p o →
           ℚ<-≤-trans p l (q (indices j) i) (ιₐ-lower⁻¹ p l o) (pr₁ (m i)))
         (λ p o → ιₐ-lower p r (ℚ<-≤-trans p (q (indices j) i) r o (pr₂ (m i))))
         (λ p o → below-the-limit (coordinate-intervals i) (succ j) p
                   (ιₐ-lower⁻¹ p l o))
         (λ p o → ιₐ-lower p r
                   (below-the-limit-gives-below-right (coordinate-intervals i)
                     (succ j) p o))

  bolzano-weierstrass
   : Σ p ꞉ ℝ^ n , Σ k ꞉ (ℕ → ℕ)
       , in-cube p
       × ((i : ℕ) → k i < k (succ i))
       × ((i : ℕ) → rational-point (q (k i)) is-within-2⁻ i of p)
  bolzano-weierstrass = limit-point , indices , limit-point-is-in-cube ,
                        indices-increase , indices-converge

\end{code}

Lemma 3.6, with the conclusion crisp.

\begin{code}

Lemma-3-6 : 𝓤₁ ̇
Lemma-3-6 =
   (@♭ n : ℕ) (@♭ q : ℕ → Fin n → ℚ)
 → (@♭ q-in-cube : (k : ℕ) → in-cube (rational-point (q k)))
 → ♭ (Σ p ꞉ ℝ^ n , Σ k ꞉ (ℕ → ℕ)
        , in-cube p
        × ((i : ℕ) → k i < k (succ i))
        × ((i : ℕ) → rational-point (q (k i)) is-within-2⁻ i of p))

Crisp-EM-gives-Lemma-3-6 : (@♭ cem : Crisp-EM 𝓤₀) → Lemma-3-6
Crisp-EM-gives-Lemma-3-6 cem n q q-in-cube =
 (bolzano-weierstrass cem q q-in-cube) ^♭

\end{code}
