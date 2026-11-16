Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026, as part of
gist.RealCohesion.CrispBolzanoWeierstrass; a module of its own, for a
general family V, since 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Bisection of rational boxes, guided by crisp excluded middle.

A box is a cube in ℚⁿ with a rational corner and a rational side. Fix a
crisp family V B K of propositions on boxes B, indexed by K : ℕ, and
say that B is often V if V B K holds for every K. Boxes have crisp
representatives (gist.RealCohesion.CrispRationals), so crisp excluded
middle decides at every box whether it is often V (decide-at). Starting
from the box of side two at a crisp corner, keep at each step a
subcube of half the side that is often V, if there is one; it is found
by exhaustive search over the 2ⁿ subcubes (TypeTopology's compactness
of finite products). The nested boxes determine a real point, which is
crisp because V and the corner are. Suppose that V B K implies V B K'
for K' ≤ K, and that whenever V B K holds, it holds for one of the
subcubes of B. Then a box that is often V has a subcube that is often
V: otherwise the largest of the bounds K beyond which its subcubes fail
V would bound the K for which the box satisfies V (pigeonhole). So
every box of the sequence is often V if the first one is.

This was the core of gist.RealCohesion.CrispBolzanoWeierstrass, written
there for the family "the sequence visits B at an index of at least K"
and the box [-1,1]ⁿ; that module is now an instance. The other instance
is gist.RealCohesion.CrispUniformContinuityOnBoxes (gate G21), where V
B K says that the values of a map at crisp rational points are not
ε-close for some pair of points within 2⁻⁽ᴷ⁺¹⁾ of each other, one of
them in B. The definitions and proofs are those of
gist.RealCohesion.CrispBolzanoWeierstrass, with the family and the
first corner as parameters.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.CrispBisection
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
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.BrouwerStatements fe pe pt using (ℝ^)
open import gist.RealCohesion.CrispRationals
open import gist.RealCohesion.NestedIntervals fe pe pt
open import gist.RealCohesion.RationalArithmetic
open import gist.RealCohesion.RealLimits fe pe pt using (ρ-becomes-small)

open PropositionalTruncation pt
open exit-truncations pt

\end{code}

Boxes. A box (a , d) is the cube of the points q with
a i ≤ q i ≤ a i + d for every i. Its subcube for c : Fin n → 𝟚 keeps,
in coordinate i, the lower half if c i ＝ ₀ and the upper half if
c i ＝ ₁ (halve, of gist.RealCohesion.RationalArithmetic).

\begin{code}

Box : ℕ → 𝓤₀ ̇
Box n = (Fin n → ℚ) × ℚ

_is-in_ : {n : ℕ} → (Fin n → ℚ) → Box n → 𝓤₀ ̇
_is-in_ {n} q (a , d) = (i : Fin n) → (a i ≤ q i) × (q i ≤ a i + d)

being-in-is-decidable : {n : ℕ} (q : Fin n → ℚ) (B : Box n)
                      → is-decidable (q is-in B)
being-in-is-decidable {n} q (a , d) =
 Fin-Π-Compact n (λ i → (a i ≤ q i) × (q i ≤ a i + d))
  (λ i → ×-preserves-decidability (ℚ≤-decide (a i) (q i))
                                  (ℚ≤-decide (q i) (a i + d)))

subcube : {n : ℕ} → (Fin n → 𝟚) → Box n → Box n
subcube c (a , d) = (λ i → halve (c i) (a i) d) , half d

\end{code}

Every point of a box lies in one of its subcubes, which can be
computed.

\begin{code}

half-containing : (x d y : ℚ) → (x + half d < y) ∔ (y ≤ x + half d) → 𝟚
half-containing x d y (inl _) = ₁
half-containing x d y (inr _) = ₀

half-contains : (x d y : ℚ) → x ≤ y → y ≤ x + d
              → (o : (x + half d < y) ∔ (y ≤ x + half d))
              → (halve (half-containing x d y o) x d ≤ y)
              × (y ≤ halve (half-containing x d y o) x d + half d)
half-contains x d y l m (inl o) = ℚ<-coarser-than-≤ (x + half d) y o ,
                                  transport (y ≤_) (add-two-halves x d ⁻¹) m
half-contains x d y l m (inr o) = l , o

subcube-containing : {n : ℕ} → Box n → (Fin n → ℚ) → Fin n → 𝟚
subcube-containing (a , d) q i =
 half-containing (a i) d (q i) (ℚ-dichotomous' (a i + half d) (q i))

subcube-contains : {n : ℕ} (B : Box n) (q : Fin n → ℚ)
                 → q is-in B → q is-in subcube (subcube-containing B q) B
subcube-contains (a , d) q k i =
 half-contains (a i) d (q i) (pr₁ (k i)) (pr₂ (k i))
  (ℚ-dichotomous' (a i + half d) (q i))

\end{code}

The 2ⁿ choices of a subcube: every function from them to ℕ is
bounded, and they can be searched exhaustively. A choice for m + 1
coordinates is a bit followed by a choice for m coordinates (Fin-cons
of gist.RealCohesion.CrispRationals).

\begin{code}

cons : {m : ℕ} → 𝟚 → (Fin m → 𝟚) → Fin (succ m) → 𝟚
cons = Fin-cons

cons-of-parts : {m : ℕ} (c : Fin (succ m) → 𝟚) → cons (c 𝟎) (c ∘ suc) ＝ c
cons-of-parts = Fin-cons-of-parts fe

functions-on-choices-are-bounded
 : (m : ℕ) (K : (Fin m → 𝟚) → ℕ) → Σ M ꞉ ℕ , ((c : Fin m → 𝟚) → K c ≤ M)
functions-on-choices-are-bounded 0        K = K e , γ
 where
  e : Fin 0 → 𝟚
  e = λ ()

  γ : (c : Fin 0 → 𝟚) → K c ≤ K e
  γ c = transport (λ - → K - ≤ K e) p (≤-refl (K e))
   where
    p : e ＝ c
    p = dfunext fe (λ ())
functions-on-choices-are-bounded (succ m) K = max M₀ M₁ , γ
 where
  IH : (b : 𝟚) → Σ M ꞉ ℕ , ((c : Fin m → 𝟚) → K (cons b c) ≤ M)
  IH b = functions-on-choices-are-bounded m (λ c → K (cons b c))

  M₀ M₁ : ℕ
  M₀ = pr₁ (IH ₀)
  M₁ = pr₁ (IH ₁)

  δ : (b : 𝟚) (c : Fin m → 𝟚) → K (cons b c) ≤ max M₀ M₁
  δ ₀ c = ≤-trans (K (cons ₀ c)) M₀ (max M₀ M₁) (pr₂ (IH ₀) c)
           (max-≤-upper-bound M₀ M₁)
  δ ₁ c = ≤-trans (K (cons ₁ c)) M₁ (max M₀ M₁) (pr₂ (IH ₁) c)
           (max-≤-upper-bound' M₁ M₀)

  γ : (c : Fin (succ m) → 𝟚) → K c ≤ max M₀ M₁
  γ c = transport (λ - → K - ≤ max M₀ M₁) (cons-of-parts c) (δ (c 𝟎) (c ∘ suc))

choices-are-Compact : (m : ℕ) → is-Compact (Fin m → 𝟚) {𝓤₀}
choices-are-Compact m =
 finitely-indexed-product-compact fe m (λ _ → 𝟚)
  (λ _ → compact-types-are-Compact 𝟚-is-compact)

\end{code}

Rational facts about the first box, [-1,1]ⁿ, and its sides. The
rational two and two facts about it are in
gist.RealCohesion.RationalArithmetic; this module re-exports them.
The next two equations are abstract. Agda's injectivity analysis
evaluates the right-hand side of each clause of a definition by
pattern matching; a closed proof about particular rationals there
makes it evaluate TypeTopology's normalization of fractions, which
took minutes.

\begin{code}

abstract
 half-of-two : half two ＝ ⟨1/2⟩^ 0
 half-of-two = half-of-double 1ℚ

 half-of-first-power : half (⟨1/2⟩^ 0) ＝ ⟨1/2⟩^ 1
 half-of-first-power = ℚ-mult-left-id 1/2

half-of-power : (j : ℕ) → half (⟨1/2⟩^ j) ＝ ⟨1/2⟩^ (succ j)
half-of-power 0        = half-of-first-power
half-of-power (succ j) = refl

\end{code}
From now on, crisp excluded middle, a crisp family V of propositions
on boxes indexed by ℕ, and a crisp corner a of the first box. V, and so
Often, is crisp, and boxes have crisp representatives, so both are
decided at every box.

\begin{code}

module bisection
        (@♭ cem : Crisp-EM 𝓤₀)
        {@♭ n : ℕ}
        (@♭ V : Box n → ℕ → 𝓤₀ ̇ )
        (@♭ V-is-prop : (B : Box n) (K : ℕ) → is-prop (V B K))
        (@♭ a : Fin n → ℚ)
       where

 Often : Box n → 𝓤₀ ̇
 Often B = (K : ℕ) → V B K

 boxes-have-crisp-representatives : has-crisp-representatives (Box n)
 boxes-have-crisp-representatives =
  ×-has-crisp-representatives
   (Fin-functions-have-crisp-representatives fe n 0ℚ
     ℚ-has-crisp-representatives)
   ℚ-has-crisp-representatives

 decide-V : (B : Box n) (K : ℕ) → is-decidable (V B K)
 decide-V B K =
  decide-at (×-has-crisp-representatives boxes-have-crisp-representatives
                                         ℕ-has-crisp-representatives)
   cem (λ (B , K) → V B K) (λ (B , K) → V-is-prop B K) (B , K)

 decide-often : (B : Box n) → is-decidable (Often B)
 decide-often =
  decide-at boxes-have-crisp-representatives cem Often
   (λ B → Π-is-prop fe (λ K → V-is-prop B K))

 decide-eventually-not : (B : Box n) → is-decidable (∃ K ꞉ ℕ , ¬ V B K)
 decide-eventually-not =
  decide-at boxes-have-crisp-representatives cem
   (λ B → ∃ K ꞉ ℕ , ¬ V B K) (λ B → ∃-is-prop)

 last : (B : Box n) → ¬ Often B → Σ K ꞉ ℕ , ¬ V B K
 last B ν = exit-truncation (λ K → ¬ V B K)
             (λ K → ¬-preserves-decidability (decide-V B K)) γ
  where
   γ : ∃ K ꞉ ℕ , ¬ V B K
   γ = Cases (decide-eventually-not B) id
        (λ μ → 𝟘-elim (ν (λ K → Cases (decide-V B K) id
                                  (λ m → 𝟘-elim (μ ∣ K , m ∣)))))

 decide-good-subcube
  : (B : Box n)
  → is-decidable (Σ c ꞉ (Fin n → 𝟚) , Often (subcube c B))
 decide-good-subcube B =
  choices-are-Compact n (λ c → Often (subcube c B))
   (λ c → decide-often (subcube c B))

 choice : (B : Box n)
        → is-decidable (Σ c ꞉ (Fin n → 𝟚) , Often (subcube c B))
        → Fin n → 𝟚
 choice B (inl (c , _)) = c
 choice B (inr _)       = λ _ → ₀

 next : Box n → Box n
 next B = subcube (choice B (decide-good-subcube B)) B

\end{code}

The nested boxes, and the point they determine.

\begin{code}

 start : Box n
 start = a , two

 stage : ℕ → Box n
 stage 0        = start
 stage (succ j) = next (stage j)

 corner : ℕ → Fin n → ℚ
 corner j = pr₁ (stage j)

 side : ℕ → ℚ
 side j = pr₂ (stage j)

 bit : ℕ → Fin n → 𝟚
 bit j = choice (stage j) (decide-good-subcube (stage j))

 side-is-nonneg : (j : ℕ) → 0ℚ ≤ side j
 side-is-nonneg 0        = two-is-nonneg
 side-is-nonneg (succ j) = half-is-nonneg (side j) (side-is-nonneg j)

 side-of-next-stage : (j : ℕ) → side (succ j) ＝ ⟨1/2⟩^ j
 side-of-next-stage 0        = half-of-two
 side-of-next-stage (succ j) = ap half (side-of-next-stage j) ∙ half-of-power j

 sides-become-small : (ε : ℚ) → 0ℚ < ε → Σ j ꞉ ℕ , side j < ε
 sides-become-small ε l = succ (succ m) ,
                          transport (_< ε) (side-of-next-stage (succ m) ⁻¹)
                           (pr₂ (ρ-becomes-small ε l))
  where
   m : ℕ
   m = pr₁ (ρ-becomes-small ε l)

 coordinate-intervals : Fin n → Nested-Intervals
 coordinate-intervals i =
  record
   { left                 = λ j → corner j i
    ; length               = side
    ; length-nonneg        = side-is-nonneg
    ; left-grows           = λ j → halve-grows (bit j i) (corner j i) (side j)
                                   (side-is-nonneg j)
    ; right-shrinks        = λ j → halve-shrinks (bit j i) (corner j i) (side j)
                                   (side-is-nonneg j)
    ; lengths-become-small = sides-become-small
    }

 limit-point : ℝ^ n
 limit-point i = limit (coordinate-intervals i)

\end{code}
Suppose that V B K implies V B K' for K' ≤ K, and that V B K holds for
one of the subcubes of B whenever it holds for B. Then a box that is
often V has a subcube that is often V, so every box of the sequence is
often V if the first one is.

\begin{code}

 module splitting
         (V-antitone : (B : Box n) (K K' : ℕ) → K ≤ K' → V B K' → V B K)
         (V-in-subcubes : (B : Box n) (K : ℕ) → V B K
                        → ∃ c ꞉ (Fin n → 𝟚) , V (subcube c B) K)
        where

  pigeonhole : (B : Box n)
             → Often B
             → ((c : Fin n → 𝟚) → ¬ Often (subcube c B))
             → 𝟘 {𝓤₀}
  pigeonhole B o ν = ∥∥-rec 𝟘-is-prop γ (V-in-subcubes B M (o M))
   where
    K : (Fin n → 𝟚) → ℕ
    K c = pr₁ (last (subcube c B) (ν c))

    M : ℕ
    M = pr₁ (functions-on-choices-are-bounded n K)

    γ : (Σ c ꞉ (Fin n → 𝟚) , V (subcube c B) M) → 𝟘
    γ (c , v) = pr₂ (last (subcube c B) (ν c))
                 (V-antitone (subcube c B) (K c) M
                   (pr₂ (functions-on-choices-are-bounded n K) c) v)

  next-is-often : (B : Box n) → Often B → Often (next B)
  next-is-often B o = γ (decide-good-subcube B)
   where
    γ : (d : is-decidable (Σ c ꞉ (Fin n → 𝟚) , Often (subcube c B)))
      → Often (subcube (choice B d) B)
    γ (inl (c , o')) = o'
    γ (inr ν)        = 𝟘-elim (pigeonhole B o (λ c o' → ν (c , o')))

  stages-are-often : Often start → (j : ℕ) → Often (stage j)
  stages-are-often o 0        = o
  stages-are-often o (succ j) = next-is-often (stage j) (stages-are-often o j)

\end{code}
