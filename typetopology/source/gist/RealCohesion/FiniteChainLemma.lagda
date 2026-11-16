Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The finite-chain lemma (Lemma 5.1 of the proof note [1]).

It is a positive form of sequential continuity: a connected interval
covered by two sets joins any two of its points through finitely many
overlaps, and each overlap changes the number of plateaus crossed by
at most one. The finiteness comes from the effectivity of the
quotient Q of levels by finite chains
(gist.RealCohesion.FiniteChainQuotient), and the connectedness from
the hypothesis that every map ℝ → Q is constant, which Axiom R♭
provides (gist.RealCohesion.FiniteChainDiscreteness).

The data:

 * a constancy hypothesis ν: every map ℝ → Q is constant;

 * a depth c : ℕ → 𝟚, which is monotone: once it is ₁, it stays ₁;

 * plateaus, open rational intervals (α j , β j) with midpoints
   α j < m j < β j, whose midpoints decrease, between two real
   endpoints, left < m j < right for every j;

 * two predicates A and D on ℝ that cover ℝ, such that A misses the
   odd plateaus of depth ₀ and D misses the even plateaus of depth ₀.
   That is, if c j ＝ ₀ and α j < z < β j, then z is not in A if j is
   odd, and z is not in D if j is even.

The conclusion is that the depth is ₁ somewhere: ∃ j , c j ＝ ₁.

In the application (gist.RealCohesion.SequentialHitting), the
plateaus accumulate at left ＝ 0, with right ＝ 1, and A and D are
the sets where a real function Γ is below 2/3 and above 1/3, where Γ
is at least 1 on the odd plateaus and below 1/4 on the even plateaus
of depth ₀. We state the lemma for A and D because it needs nothing
else about Γ, so that this module only compares real numbers with
rationals.

The proof. For z in A and an odd plateau j of depth ₀, z isn't in the
plateau, so it lies on one side of its midpoint, and which side is
decidable: by locatedness, z < m j or α j < z, and in the second case
m j < z or z < β j, which is impossible. The level x z of z in A has
a 1 at position k exactly when the k-th odd plateau has depth ₀ and
lies to the right of z. Similarly the level y z of z in D counts the
even plateaus of depth ₀ to the right of z. For z in both A and D the
two levels are adjacent, because the plateaus alternate. So
Λ z := [ x z ] on A and [ y z ] on D is a well-defined map ℝ → Q,
hence constant. At the right endpoint both levels are zero. At the
left endpoint, the levels list the depths of the odd and even
plateaus. So the class of one of them is the class of the zero level,
and effectivity gives a position where it has a 0, that is, a
plateau of depth ₁.

Unlike [1], we index the odd plateaus 2k + 1 and the even plateaus
2k + 2 by k, recursively, so that the index arithmetic is
definitional.

[1] The approximate intermediate value theorem from real cohesion
    alone. Proof note by Claude Fable 5.2, revision 2, 10 November
    2026, audited by GPT-6 Astra.
    references/F17-aivt-proof-rev2.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.FiniteChainLemma
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import MLTT.Two-Properties
open import Notation.Order
open import Rationals.Order
open import Rationals.Type
open import UF.Powerset
open import UF.Sets
open import UF.Subsingletons-FunExt
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.FiniteChainLevels
open import gist.RealCohesion.FiniteChainQuotient fe pe pt

open PropositionalTruncation pt

\end{code}

The odd and the even plateau indices, 2k + 1 and 2k + 2.

\begin{code}

odd-index : ℕ → ℕ
odd-index 0        = 1
odd-index (succ k) = succ (succ (odd-index k))

even-index : ℕ → ℕ
even-index k = succ (odd-index k)

\end{code}

The bit of a decision.

\begin{code}

bit : {𝓤 𝓥 : Universe} {P : 𝓤 ̇ } {R : 𝓥 ̇ } → P + R → 𝟚
bit (inl _) = ₁
bit (inr _) = ₀

bit-is-₁ : {𝓤 𝓥 : Universe} {P : 𝓤 ̇ } {R : 𝓥 ̇ } (d : P + R) → bit d ＝ ₁ → P
bit-is-₁ (inl p) _ = p
bit-is-₁ (inr _) e = 𝟘-elim (zero-is-not-one e)

bit-is-₀ : {𝓤 𝓥 : Universe} {P : 𝓤 ̇ } {R : 𝓥 ̇ } (d : P + R) → bit d ＝ ₀ → R
bit-is-₀ (inl _) e = 𝟘-elim (one-is-not-zero e)
bit-is-₀ (inr r) _ = r

\end{code}

The data of the lemma, as module parameters.

\begin{code}

module finite-chain-lemma
        (ν : (h : ℝ → Q) (u v : ℝ) → h u ＝ h v)
        (c : ℕ → 𝟚)
        (c-is-monotone : (j : ℕ) → c j ＝ ₁ → c (succ j) ＝ ₁)
        (left right : ℝ)
        (α m β : ℕ → ℚ)
        (α-below-m : (j : ℕ) → α j < m j)
        (m-below-β : (j : ℕ) → m j < β j)
        (m-decreases : (j : ℕ) → m (succ j) < m j)
        (left-below-m : (j : ℕ) → left < m j)
        (m-below-right : (j : ℕ) → m j < right)
        {𝓥 : Universe}
        (A D : ℝ → 𝓥 ̇ )
        (A-is-prop-valued : (z : ℝ) → is-prop (A z))
        (D-is-prop-valued : (z : ℝ) → is-prop (D z))
        (cover : (z : ℝ) → A z ∨ D z)
        (A-misses-odd-plateaus : (k : ℕ) → c (odd-index k) ＝ ₀
                               → (z : ℝ) → A z
                               → α (odd-index k) < z → z < β (odd-index k)
                               → 𝟘 {𝓤₀})
        (D-misses-even-plateaus : (k : ℕ) → c (even-index k) ＝ ₀
                                → (z : ℝ) → D z
                                → α (even-index k) < z → z < β (even-index k)
                                → 𝟘 {𝓤₀})
       where

\end{code}

The depth is ₀ below a place where it is ₀, and the midpoints
decrease.

\begin{code}

 c-is-₀-below : (j : ℕ) → c (succ j) ＝ ₀ → c j ＝ ₀
 c-is-₀-below j e = different-from-₁-equal-₀
                     (λ p → zero-is-not-one (e ⁻¹ ∙ c-is-monotone j p))

 below-a-later-midpoint : (z : ℝ) (j : ℕ) → z < m (succ j) → z < m j
 below-a-later-midpoint z j l = use-rounded-real-R z (m (succ j)) (m j)
                                 (m-decreases j) l

\end{code}

Sides. A real number outside a plateau lies on a decidable side of its
midpoint.

\begin{code}

 sides-are-exclusive : (z : ℝ) (q : ℚ) → z < q → q < z → 𝟘 {𝓤₀}
 sides-are-exclusive z q l l' = ℚ<-irrefl q (disjoint-from-real z q q (l' , l))

 sides-is-prop : (z : ℝ) (q : ℚ) → is-prop ((z < q) + (q < z))
 sides-is-prop z q = +-is-prop (∈-is-prop (upper-cut-of z) q)
                               (∈-is-prop (lower-cut-of z) q)
                               (sides-are-exclusive z q)

 sides : (z : ℝ) (j : ℕ)
       → (α j < z → z < β j → 𝟘 {𝓤₀})
       → (z < m j) + (m j < z)
 sides z j outside = ∥∥-rec (sides-is-prop z (m j)) γ
                      (ℝ-locatedness z (α j) (m j) (α-below-m j))
  where
   γ : (α j < z) + (z < m j) → (z < m j) + (m j < z)
   γ (inr l) = inl l
   γ (inl l) = ∥∥-rec (sides-is-prop z (m j)) δ
                (ℝ-locatedness z (m j) (β j) (m-below-β j))
    where
     δ : (m j < z) + (z < β j) → (z < m j) + (m j < z)
     δ (inl l') = inr l'
     δ (inr l') = 𝟘-elim (outside l l')

 sides-on-the-left : (z : ℝ) (j : ℕ) (o : α j < z → z < β j → 𝟘)
                   → (l : z < m j) → sides z j o ＝ inl l
 sides-on-the-left z j o l = sides-is-prop z (m j) (sides z j o) (inl l)

\end{code}

The levels. The level of z in A has a 1 at position k exactly when
the plateau odd-index k has depth ₀ and lies to the right of z, and
similarly for D and the even plateaus. Both are instances of one
construction, for a predicate P and plateau indices idx that P misses
where the depth is ₀.

\begin{code}

 module levels-of
         (P : ℝ → 𝓥 ̇ )
         (idx : ℕ → ℕ)
         (P-misses-plateaus : (k : ℕ) → c (idx k) ＝ ₀
                            → (z : ℝ) → P z
                            → α (idx k) < z → z < β (idx k) → 𝟘 {𝓤₀})
        where

  level-bit : (z : ℝ) → P z → (k : ℕ) (b : 𝟚) → c (idx k) ＝ b → 𝟚
  level-bit z p k ₀ e = bit (sides z (idx k) (P-misses-plateaus k e z p))
  level-bit z p k ₁ e = ₀

  level : (z : ℝ) → P z → Level
  level z p k = level-bit z p k (c (idx k)) refl

  level-is-₁ : (z : ℝ) (p : P z) (k : ℕ)
             → level z p k ＝ ₁
             → (c (idx k) ＝ ₀) × (z < m (idx k))
  level-is-₁ z p k = γ (c (idx k)) refl
   where
    γ : (b : 𝟚) (e : c (idx k) ＝ b)
      → level-bit z p k b e ＝ ₁
      → (c (idx k) ＝ ₀) × (z < m (idx k))
    γ ₀ e q = e , bit-is-₁ (sides z (idx k) (P-misses-plateaus k e z p)) q
    γ ₁ e q = 𝟘-elim (zero-is-not-one q)

  level-is-₁-if : (z : ℝ) (p : P z) (k : ℕ)
                → c (idx k) ＝ ₀
                → z < m (idx k)
                → level z p k ＝ ₁
  level-is-₁-if z p k e₀ l = γ (c (idx k)) refl
   where
    γ : (b : 𝟚) (e : c (idx k) ＝ b) → level-bit z p k b e ＝ ₁
    γ ₀ e = ap bit (sides-on-the-left z (idx k) (P-misses-plateaus k e z p) l)
    γ ₁ e = 𝟘-elim (zero-is-not-one (e₀ ⁻¹ ∙ e))

  level-at-right : (p : P right) → level right p ＝ zero-level
  level-at-right p = dfunext fe γ
   where
    γ : (k : ℕ) → level right p k ＝ ₀
    γ k = different-from-₁-equal-₀
           (λ q → sides-are-exclusive right (m (idx k))
                   (pr₂ (level-is-₁ right p k q))
                   (m-below-right (idx k)))

  zero-of-level-at-left : (p : P left) (k : ℕ)
                        → level left p k ＝ ₀ → c (idx k) ＝ ₁
  zero-of-level-at-left p k q =
   different-from-₀-equal-₁
    (λ e →
      zero-is-not-one (q ⁻¹ ∙ level-is-₁-if left p k e (left-below-m (idx k))))

 open levels-of A odd-index A-misses-odd-plateaus
  using ()
  renaming (level-bit to x-bit ; level to x-level ; level-is-₁ to x-level-is-₁ ;
            level-is-₁-if to x-level-is-₁-if ;
             level-at-right to x-level-at-right ;
            zero-of-level-at-left to zero-of-x-level-at-left)
  public

 open levels-of D even-index D-misses-even-plateaus
  using ()
  renaming (level-bit to y-bit ; level to y-level ; level-is-₁ to y-level-is-₁ ;
            level-is-₁-if to y-level-is-₁-if ;
             level-at-right to y-level-at-right ;
            zero-of-level-at-left to zero-of-y-level-at-left)
  public

\end{code}

Adjacency. Let z be in A and in D. If the odd plateau 2k + 3 has depth
₀ and lies to the right of z, then so does the even plateau 2k + 2,
which comes before it. If the even plateau 2k + 4 has depth ₀ and lies
to the right of z, then so does the odd plateau 2k + 1.

\begin{code}

 levels-are-adjacent : (z : ℝ) (a : A z) (d : D z)
                     → Adj (x-level z a) (y-level z d)
 levels-are-adjacent z a d = I , II
  where
   I : x-level z a ⪯ y-level z d
   I k p = y-level-is-₁-if z d k
            (c-is-₀-below (even-index k) e)
            (below-a-later-midpoint z (even-index k) l)
    where
     e : c (succ (even-index k)) ＝ ₀
     e = pr₁ (x-level-is-₁ z a (succ k) p)

     l : z < m (succ (even-index k))
     l = pr₂ (x-level-is-₁ z a (succ k) p)

   II : y-level z d ⪯ x-level z a
   II k p = x-level-is-₁-if z a k
             (c-is-₀-below j
               (c-is-₀-below (succ j) (c-is-₀-below (succ (succ j)) e)))
             (below-a-later-midpoint z j
               (below-a-later-midpoint z (succ j)
                 (below-a-later-midpoint z (succ (succ j)) l)))
    where
     j : ℕ
     j = odd-index k

     e : c (succ (succ (succ j))) ＝ ₀
     e = pr₁ (y-level-is-₁ z d (succ k) p)

     l : z < m (succ (succ (succ j)))
     l = pr₂ (y-level-is-₁ z d (succ k) p)

\end{code}

The level map Λ : ℝ → Q. For each z, the type of classes q such that
q is the class of the level of z in A if z is in A, and the class of
its level in D if z is in D, is a proposition, because z is merely in
A or in D and Q is a set. It is inhabited, again by the cover, now
because the goal is a proposition, and by adjacency. So it has a
unique element, which we call Λ z. No truncation is eliminated into
a type that is not a proposition.

\begin{code}

 Λ-type : ℝ → 𝓤₁ ⊔ 𝓥 ̇
 Λ-type z = Σ q ꞉ Q , ((a : A z) → q ＝ [ x-level z a ])
                    × ((d : D z) → q ＝ [ y-level z d ])

 Λ-type-is-prop : (z : ℝ) → is-prop (Λ-type z)
 Λ-type-is-prop z (q , f , g) (q' , f' , g') =
  to-subtype-＝
   (λ q → ×-is-prop (Π-is-prop fe (λ a → Q-is-set))
                    (Π-is-prop fe (λ d → Q-is-set)))
   (∥∥-rec Q-is-set γ (cover z))
  where
   γ : A z + D z → q ＝ q'
   γ (inl a) = f a ∙ f' a ⁻¹
   γ (inr d) = g d ∙ g' d ⁻¹

 Λ-type-is-inhabited : (z : ℝ) → Λ-type z
 Λ-type-is-inhabited z = ∥∥-rec (Λ-type-is-prop z) γ (cover z)
  where
   γ : A z + D z → Λ-type z
   γ (inl a) = [ x-level z a ] ,
               (λ a' → ap (λ - → [ x-level z - ]) (A-is-prop-valued z a a')) ,
               (λ d → adjacent-levels-have-the-same-class
                       (x-level z a) (y-level z d) (levels-are-adjacent z a d))
   γ (inr d) = [ y-level z d ] ,
               (λ a → adjacent-levels-have-the-same-class
                       (x-level z a) (y-level z d) (levels-are-adjacent z a d)
                        ⁻¹) ,
               (λ d' → ap (λ - → [ y-level z - ]) (D-is-prop-valued z d d'))

 Λ : ℝ → Q
 Λ z = pr₁ (Λ-type-is-inhabited z)

 Λ-on-A : (z : ℝ) (a : A z) → Λ z ＝ [ x-level z a ]
 Λ-on-A z = pr₁ (pr₂ (Λ-type-is-inhabited z))

 Λ-on-D : (z : ℝ) (d : D z) → Λ z ＝ [ y-level z d ]
 Λ-on-D z = pr₂ (pr₂ (Λ-type-is-inhabited z))

\end{code}

The endpoints. Every plateau lies to the left of the right endpoint,
so both levels there are zero (level-at-right above), and so is Λ.
Every plateau lies to the right of the left endpoint, so the levels
there have a 0 only at plateaus of depth ₁ (zero-of-level-at-left
above).

\begin{code}

 Λ-at-right : Λ right ＝ [ zero-level ]
 Λ-at-right = ∥∥-rec Q-is-set γ (cover right)
  where
   γ : A right + D right → Λ right ＝ [ zero-level ]
   γ (inl a) = Λ-on-A right a ∙ ap [_] (x-level-at-right a)
   γ (inr d) = Λ-on-D right d ∙ ap [_] (y-level-at-right d)

\end{code}

The conclusion.

\begin{code}

 depth-is-somewhere-₁ : ∃ j ꞉ ℕ , c j ＝ ₁
 depth-is-somewhere-₁ = ∥∥-rec ∃-is-prop γ (cover left)
  where
   e : Λ left ＝ [ zero-level ]
   e = ν Λ left right ∙ Λ-at-right

   γ : A left + D left → ∃ j ꞉ ℕ , c j ＝ ₁
   γ (inl a) = ∥∥-functor
                (λ (k , p) → odd-index k , zero-of-x-level-at-left a k p)
                (class-of-zero-gives-zero-bit (x-level left a)
                  (Λ-on-A left a ⁻¹ ∙ e))
   γ (inr d) = ∥∥-functor
                (λ (k , p) → even-index k , zero-of-y-level-at-left d k p)
                (class-of-zero-gives-zero-bit (y-level left d)
                  (Λ-on-D left d ⁻¹ ∙ e))

\end{code}
