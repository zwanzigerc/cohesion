Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

GPT-6 Astra's digit-interleaving curve P : ℝ → ℝ^m, for gate G24 of
Claude Fable 5.2's second addendum: the curve of Lemma 7.16 of the
write-up [1], with the values that the proof of Theorem 7.17 uses.

The definition. d t = clamp 0 1 (3t - 1) reads a ternary digit, and
S t = 3t - 2 d(t) shifts it away; both are real functions built from
sums, negation and clamps. The i-th coordinate of P t, for i < m, is
the sum over k of the readings at the places m·k + i, with weight
2⁻⁽ᵏ⁺²⁾: the series of gist.RealCohesion.PositiveTerms with terms
clamp 0 2⁻⁽ᵏ⁺²⁾ (3·Sᵐᵏ⁺ⁱ(t) - 1), which Fable suggests in place of
2⁻⁽ᵏ⁺²⁾·d(Sᵐᵏ⁺ⁱ(t)) (the two agree when the reading is 0 or 1). So P is
half of Astra's curve; the factor is harmless, and it lets the series
of gist.RealCohesion.PositiveTerms serve unchanged. Only the values of
P at rational points matter, and P has no free variable but m.

The values, from the rational arithmetic of gist.RealCohesion.DigitCodes
and gist.RealCohesion.DigitCells:

 * at a rational point L b y with y in [0, 1], the reading is b and
   the shift is y; so along a block orbit the readings are the bits
   of the blocks;

 * at the code of a rational vector w at level K, the i-th coordinate
   of P is the weighted sum of the first K binary digits of w i,
   which is within 2⁻⁽ᴷ⁺¹⁾ below (w i)/2;

 * at the centre 1/4, the i-th coordinate of P is half of 1/3 or of
   2/3, alternately, for blocks of odd length m.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revision of 12 November 2026, Lemma 7.16.
    references/C04-write-up-2026-11-12.tex

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.DigitCurve
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import MLTT.List using (List ; [] ; _∷_ ; length)
open import Fin.Type using (Fin ; 𝟎 ; suc)
open import UF.Base using (ap₂ ; transport₂)
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Multiplication renaming (_*_ to _*ℕ_)
open import Naturals.Order
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealLattice fe pe pt
 using (clamp ; clamp-below ; clamp-above ; ιₐ-≤-ιₐ ; ιₐ-sum ;
         equal-if-lower-cuts-agree ;
        below-neg ; below-neg⁻¹ ; min ; positive-min ; positive-min⁻¹ ;
         Fin-min ;
        Fin-min-is-positive ; positive-Fin-min ; <-from-difference ;
         <-gives-positive-difference)
 renaming (_+_ to _ℝ+_ ; -_ to ℝ-_)
open import gist.RealCohesion.RealLimits fe pe pt
 using (ρ ; ρ-antitone ; within ; within-weaken ; within-from-bounds ;
         minus-nonneg-is-below ;
        module geometric-limit)
open import Rationals.Limits fe pe pt using (⟨1/2⟩^_)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.FunctionalHitting fe pe pt
 using (_is-within-2⁻_of_ ; positive-sequential-hitting-for-functionals ;
         rational-from-positive)
open import gist.RealCohesion.SequentialHitting fe pe pt
 using (starter-bounds-from-within ; positive-from-rational)
open import gist.RealCohesion.StrongExtensionality fe pe pt
 using (ρ-is-below-power)
import gist.RealCohesion.RationalDetection fe pe pt as RD
import gist.RealCohesion.PositiveTerms fe pe pt as PT
open import gist.RealCohesion.RationalArithmetic
 using (half ; half-of-double ; halves-add-up)
open import gist.RealCohesion.DigitCodes
open import gist.RealCohesion.DigitCells

open PropositionalTruncation pt

\end{code}

The embedding of the rationals commutes with negation.

\begin{code}

ιₐ-neg : (q : ℚ) → ℝ- (ιₐ q) ＝ ιₐ (ℚ- q)
ιₐ-neg q = equal-if-lower-cuts-agree (ℝ- (ιₐ q)) (ιₐ (ℚ- q)) I II
 where
  I : (p : ℚ) → p < (ℝ- (ιₐ q)) → p < ιₐ (ℚ- q)
  I p l = ιₐ-lower p (ℚ- q)
           (transport (_< ℚ- q) (ℚ-minus-minus p ⁻¹)
             (ℚ<-swap q (ℚ- p) (ιₐ-upper⁻¹ q (ℚ- p) (below-neg⁻¹ (ιₐ q) p l))))

  II : (p : ℚ) → p < ιₐ (ℚ- q) → p < (ℝ- (ιₐ q))
  II p l = transport (_< (ℝ- (ιₐ q))) (ℚ-minus-minus p ⁻¹)
            (below-neg (ιₐ q) (ℚ- p)
              (ιₐ-upper q (ℚ- p)
                (transport (_< ℚ- p) (ℚ-minus-minus q ⁻¹)
                  (ℚ<-swap p (ℚ- q) (ιₐ-lower⁻¹ p (ℚ- q) l)))))

\end{code}

The reading and the shift, and their iterates.

\begin{code}

triple-ℝ : ℝ → ℝ
triple-ℝ u = (u ℝ+ u) ℝ+ u

reading-argument : ℝ → ℝ
reading-argument u = triple-ℝ u ℝ+ ιₐ (ℚ- 1ℚ)

d : ℝ → ℝ
d u = clamp (ιₐ 0ℚ) (ιₐ 1ℚ) (reading-argument u)

S : ℝ → ℝ
S u = triple-ℝ u ℝ+ (ℝ- (d u ℝ+ d u))

S^ : ℕ → ℝ → ℝ
S^ 0        u = u
S^ (succ k) u = S^ k (S u)

S^-commutes : (a : ℕ) (u : ℝ) → S^ a (S u) ＝ S (S^ a u)
S^-commutes 0        u = refl
S^-commutes (succ a) u = S^-commutes a (S u)

S^-sum : (a b : ℕ) (u : ℝ) → S^ (a +ℕ b) u ＝ S^ b (S^ a u)
S^-sum a 0        u = refl
S^-sum a (succ b) u = S^-sum a b (S u) ∙ ap (S^ b) (S^-commutes a u)

\end{code}

Readings at rational points L b y with y in [0, 1].

\begin{code}

ιₐ-triple : (x : ℚ) → triple-ℝ (ιₐ x) ＝ ιₐ (triple x)
ιₐ-triple x = ap (_ℝ+ ιₐ x) (ιₐ-sum x x) ∙ ιₐ-sum (x ℚ+ x) x

argument-at : (x : ℚ) → reading-argument (ιₐ x) ＝ ιₐ (triple x ℚ- 1ℚ)
argument-at x = ap (_ℝ+ ιₐ (ℚ- 1ℚ)) (ιₐ-triple x) ∙ ιₐ-sum (triple x) (ℚ- 1ℚ)

d-at-L : (b : 𝟚) (y : ℚ) → y ∈𝕀 → d (ιₐ (L b y)) ＝ ιₐ (bit b)
d-at-L ₀ y (l , m) =
 clamp-below (ιₐ 0ℚ) (ιₐ 1ℚ) (reading-argument (ιₐ (L ₀ y)))
  (transport (_≤ ιₐ 0ℚ) (argument-at (L ₀ y) ⁻¹)
    (ιₐ-≤-ιₐ (triple (L ₀ y) ℚ- 1ℚ) 0ℚ (argument-of-L₀ y m)))
d-at-L ₁ y (l , m) =
 clamp-above (ιₐ 0ℚ) (ιₐ 1ℚ) (reading-argument (ιₐ (L ₁ y)))
  (ιₐ-≤-ιₐ 0ℚ 1ℚ (ℚ<-coarser-than-≤ 0ℚ 1ℚ 0<1))
  (transport (ιₐ 1ℚ ≤_) (argument-at (L ₁ y) ⁻¹)
    (ιₐ-≤-ιₐ 1ℚ (triple (L ₁ y) ℚ- 1ℚ) (argument-of-L₁ y l)))

S-at-L : (b : 𝟚) (y : ℚ) → y ∈𝕀 → S (ιₐ (L b y)) ＝ ιₐ y
S-at-L b y i = ap₂ _ℝ+_ (ιₐ-triple (L b y))
                (ap ℝ-_
                  (ap (λ t → t ℝ+ t) (d-at-L b y i) ∙ ιₐ-sum (bit b) (bit b))
                 ∙ ιₐ-neg (bit b ℚ+ bit b))
             ∙ ιₐ-sum (triple (L b y)) (ℚ- (bit b ℚ+ bit b))
             ∙ ap ιₐ (shift-of-L b y)

term-at-L : (b : 𝟚) (y : ℚ) → y ∈𝕀 → (k : ℕ)
          → clamp (ιₐ 0ℚ) (ιₐ (ρ (succ k))) (reading-argument (ιₐ (L b y)))
          ＝ ιₐ (scaled b (ρ (succ k)))
term-at-L ₀ y (l , m) k =
 clamp-below (ιₐ 0ℚ) (ιₐ (ρ (succ k))) (reading-argument (ιₐ (L ₀ y)))
  (transport (_≤ ιₐ 0ℚ) (argument-at (L ₀ y) ⁻¹)
    (ιₐ-≤-ιₐ (triple (L ₀ y) ℚ- 1ℚ) 0ℚ (argument-of-L₀ y m)))
term-at-L ₁ y (l , m) k =
 clamp-above (ιₐ 0ℚ) (ιₐ (ρ (succ k))) (reading-argument (ιₐ (L ₁ y)))
  (ιₐ-≤-ιₐ 0ℚ (ρ (succ k)) (pow½-is-nonneg (succ (succ k))))
  (transport (ιₐ (ρ (succ k)) ≤_) (argument-at (L ₁ y) ⁻¹)
    (ιₐ-≤-ιₐ (ρ (succ k)) (triple (L ₁ y) ℚ- 1ℚ)
      (ℚ≤-trans (ρ (succ k)) 1ℚ (triple (L ₁ y) ℚ- 1ℚ)
        (pow½-at-most-one (succ (succ k))) (argument-of-L₁ y l))))

\end{code}

Through a block, and along a block orbit.

\begin{code}

S^-through-block : (bs : List 𝟚) (y : ℚ) → y ∈𝕀
                 → S^ (length bs) (ιₐ (Lblock bs y)) ＝ ιₐ y
S^-through-block []       y i = refl
S^-through-block (b ∷ bs) y i =
 ap (S^ (length bs)) (S-at-L b (Lblock bs y) (Lblock-in-𝕀 bs y i))
                              ∙ S^-through-block bs y i

S^-into-block : (bs : List 𝟚) (y : ℚ) → y ∈𝕀 → (i : ℕ) → i <ℕ length bs
              → S^ i (ιₐ (Lblock bs y)) ＝ ιₐ (Lblock (drop i bs) y)
S^-into-block []       y v i        l = 𝟘-elim l
S^-into-block (b ∷ bs) y v 0        l = refl
S^-into-block (b ∷ bs) y v (succ i) l =
 ap (S^ i) (S-at-L b (Lblock bs y) (Lblock-in-𝕀 bs y v))
                                      ∙ S^-into-block bs y v i l

module block-orbit
        (m : ℕ)
        (z : ℕ → ℚ)
        (B : ℕ → ℕ → 𝟚)
        (z-in-𝕀 : (q : ℕ) → z q ∈𝕀)
        (z-orbit : (q : ℕ) → z q ＝ Lblock (blockOf (succ m) (B q)) (z (succ q)))
       where

 after-blocks : (k j : ℕ) → S^ (succ m *ℕ k) (ιₐ (z j)) ＝ ιₐ (z (j +ℕ k))
 after-blocks 0        j = refl
 after-blocks (succ k) j =
    S^-sum (succ m) (succ m *ℕ k) (ιₐ (z j))
  ∙ ap (S^ (succ m *ℕ k)) I
  ∙ after-blocks k (succ j)
  ∙ ap (λ x → ιₐ (z x)) (succ-left j k)
  where
   I : S^ (succ m) (ιₐ (z j)) ＝ ιₐ (z (succ j))
   I = ap (λ t → S^ (succ m) (ιₐ t)) (z-orbit j)
     ∙ transport (λ x → S^ x (ιₐ (Lblock (blockOf (succ m) (B j)) (z (succ j))))
                        ＝ ιₐ (z (succ j)))
                 (length-of-blockOf (succ m) (B j))
                 (S^-through-block (blockOf (succ m) (B j)) (z (succ j))
                   (z-in-𝕀 (succ j)))

 point-of-reading : (k i : ℕ) → i <ℕ succ m → ℚ
 point-of-reading k i l =
  Lblock (drop (succ i) (blockOf (succ m) (B k))) (z (succ k))

 point-of-reading-in-𝕀 : (k i : ℕ) (l : i <ℕ succ m) → point-of-reading k i l ∈𝕀
 point-of-reading-in-𝕀 k i l =
  Lblock-in-𝕀 (drop (succ i) (blockOf (succ m) (B k))) (z (succ k))
                                (z-in-𝕀 (succ k))

 reading-place : (k i : ℕ) (l : i <ℕ succ m)
               → S^ (succ m *ℕ k +ℕ i) (ιₐ (z 0))
               ＝ ιₐ (L (B k i) (point-of-reading k i l))
 reading-place k i l =
    S^-sum (succ m *ℕ k) i (ιₐ (z 0))
  ∙ ap (S^ i) (after-blocks k 0 ∙ ap (λ x → ιₐ (z x)) (zero-left-neutral k)
               ∙ ap ιₐ (z-orbit k))
  ∙ S^-into-block (blockOf (succ m) (B k)) (z (succ k)) (z-in-𝕀 (succ k)) i l'
  ∙ ap ιₐ (Lblock-drop (blockOf (succ m) (B k)) (z (succ k)) i l'
           ∙ ap (λ c → L c (point-of-reading k i l))
              (letter-of-blockOf (succ m) (B k) i l))
  where
   l' : i <ℕ length (blockOf (succ m) (B k))
   l' = transport (i <ℕ_) (length-of-blockOf (succ m) (B k) ⁻¹) l

\end{code}

The curve. It is abstract, with its defining equation P-is: P is built
from functions of this module, which has the parameter fe : Fun-Ext,
and when another module compared values of P instantiated there, Agda
unfolded the limit that defines them (gist.RealCohesion.RationalGrid
explains the cause).

\begin{code}

coordinate-terms : ℕ → ℕ → ℝ → ℕ → ℝ
coordinate-terms m i t k = reading-argument (S^ (succ m *ℕ k +ℕ i) t)

abstract
 P : ℕ → ℕ → ℝ → ℝ
 P m i t = PT.sum (coordinate-terms m i t)

 P-is : (m i : ℕ) (t : ℝ) → P m i t ＝ PT.sum (coordinate-terms m i t)
 P-is m i t = refl

\end{code}

The partial sums of P along a block orbit are the digit sums of the
blocks.

\begin{code}

module values
        (m : ℕ)
        (z : ℕ → ℚ)
        (B : ℕ → ℕ → 𝟚)
        (z-in-𝕀 : (q : ℕ) → z q ∈𝕀)
        (z-orbit : (q : ℕ) → z q ＝ Lblock (blockOf (succ m) (B q)) (z (succ q)))
        (i : ℕ)
        (l : i <ℕ succ m)
       where

 open block-orbit m z B z-in-𝕀 z-orbit

 partial-sums : (N : ℕ)
              → PT.partial-sum (coordinate-terms m i (ιₐ (z 0))) N
              ＝ ιₐ (DS (λ k → B k i) N)
 partial-sums 0        = refl
 partial-sums (succ N) =
    ap₂ _ℝ+_ (partial-sums N)
      (ap (λ t → clamp (ιₐ 0ℚ) (ιₐ (ρ (succ N))) (reading-argument t))
        (reading-place N i l)
       ∙ term-at-L (B N i) (point-of-reading N i l)
          (point-of-reading-in-𝕀 N i l) N)
  ∙ ιₐ-sum (DS (λ k → B k i) N) (scaled (B N i) (ρ (succ N)))

\end{code}

Digit sums of eventually zero digits, and of equal digits.

\begin{code}

DS-eventually-constant : (f : ℕ → 𝟚) (K : ℕ) → ((k : ℕ) → K ≤ℕ k → f k ＝ ₀)
                       → (d : ℕ) → DS f (K +ℕ d) ＝ DS f K
DS-eventually-constant f K z 0        = refl
DS-eventually-constant f K z (succ d) =
   ap (λ c → DS f (K +ℕ d) ℚ+ scaled c (ρ (succ (K +ℕ d))))
    (z (K +ℕ d) (≤-+ K d))
 ∙ ℚ-zero-right-neutral (DS f (K +ℕ d))
 ∙ DS-eventually-constant f K z d

DS-ext : (f g : ℕ → 𝟚) (N : ℕ) → ((k : ℕ) → k <ℕ N → f k ＝ g k)
       → DS f N ＝ DS g N
DS-ext f g 0        e = refl
DS-ext f g (succ N) e = ap₂ (λ x c → x ℚ+ scaled c (ρ (succ N)))
                         (DS-ext f g N (λ k l →
                           e k (≤-trans (succ k) N (succ N) l (≤-succ N))))
                         (e N (<-succ N))

\end{code}

P at codes.

\begin{code}

P-at-code : (m K : ℕ) (w : ℕ → ℚ) (i : ℕ) → i <ℕ succ m
          → P m i (ιₐ (code (succ m) K w)) ＝ ιₐ (DS (digits (w i)) K)
P-at-code m K w i l =
   P-is m i (ιₐ (code (succ m) K w))
 ∙ geometric-limit.lim-of-eventually-constant
    (PT.partial-sum (coordinate-terms m i (ιₐ (code (succ m) K w))))
    (PT.step (coordinate-terms m i (ιₐ (code (succ m) K w))))
    (ιₐ (DS (digits (w i)) K)) K γ
 where
  open values m (code-point (succ m) K w) (λ q j → dig K w q j)
              (code-point-in-𝕀 (succ m) K w) (code-orbit (succ m) K w) i l

  γ : (e : ℕ)
    → PT.partial-sum (coordinate-terms m i (ιₐ (code (succ m) K w))) (K +ℕ e)
              ＝ ιₐ (DS (digits (w i)) K)
  γ e = partial-sums (K +ℕ e)
      ∙ ap ιₐ (DS-eventually-constant (λ k → dig K w k i) K
                (λ k o → dig-beyond K w k i o) e
               ∙ DS-ext (λ k → dig K w k i) (digits (w i)) K
                  (λ k o → dig-is-digits K w k i o))

\end{code}

P at the centre 1/4, for blocks of odd length succ (dbl n): its i-th
coordinate is half the centre of the cells of coordinate i.

\begin{code}

centre-digits : (b : 𝟚) (k : ℕ) → digits (centre-of b) k ＝ altfrom b k
centre-digits b k =
 cell-digits (succ k) b (centre-of b) (centre-is-in-its-cells (succ k) b) k
                     (<-succ k)

within-of-bounds : (a c e : ℚ) → 0ℚ ≤ e → a ≤ c → c < a ℚ+ e
                 → within e (ιₐ a) (ιₐ c)
within-of-bounds a c e o k k' =
 within-from-bounds e (ιₐ a) (ιₐ c)
  (transport (_≤ ιₐ c) (ιₐ-sum a (ℚ- e) ⁻¹)
    (ιₐ-≤-ιₐ (a ℚ- e) c
      (ℚ≤-trans (a ℚ- e) a c (minus-nonneg-is-below a e o) k)))
  (transport (ιₐ c ≤_) (ιₐ-sum a e ⁻¹)
    (ιₐ-≤-ιₐ c (a ℚ+ e) (ℚ<-coarser-than-≤ c (a ℚ+ e) k')))

P-at-centre : (n i : ℕ) → i <ℕ succ (dbl n)
            → P (dbl n) i (ιₐ 1/4) ＝ ιₐ (half (centre-of (alt i)))
P-at-centre n i l =
 P-is (dbl n) i (ιₐ 1/4)
 ∙ geometric-limit.lim-of-approximations
  (PT.partial-sum (coordinate-terms (dbl n) i (ιₐ 1/4)))
  (PT.step (coordinate-terms (dbl n) i (ιₐ 1/4)))
  (ιₐ (half (centre-of (alt i)))) γ
 where
  open values (dbl n) (λ q → point (alt q)) (λ q → altfrom (alt q))
              (λ q → point-in-𝕀 (alt q)) (centre-orbit n) i l

  e : (N : ℕ)
    → DS (λ k → altfrom (alt k) i) N ＝ DS (digits (centre-of (alt i))) N
  e N = DS-ext (λ k → altfrom (alt k) i) (digits (centre-of (alt i))) N
         (λ k o → alt-swap k i ∙ centre-digits (alt i) k ⁻¹)

  γ : (N : ℕ)
    → within (ρ N) (PT.partial-sum (coordinate-terms (dbl n) i (ιₐ 1/4)) N)
                         (ιₐ (half (centre-of (alt i))))
  γ N = transport (λ t → within (ρ N) t (ιₐ (half (centre-of (alt i)))))
         ((partial-sums N ∙ ap ιₐ (e N)) ⁻¹)
         (within-of-bounds (DS (digits (centre-of (alt i))) N)
           (half (centre-of (alt i))) (ρ N)
           (pow½-is-nonneg (succ N))
           (pr₁ (DS-bounds N (centre-of (alt i))
                  (cell-in-𝕁 0 (alt i) (centre-of (alt i))
                  (centre-is-in-its-cells 0 (alt i)))))
           (pr₂ (DS-bounds N (centre-of (alt i))
                  (cell-in-𝕁 0 (alt i) (centre-of (alt i))
                  (centre-is-in-its-cells 0 (alt i))))))

\end{code}

Detection along the curve, for blocks of length 2n + 1. A point of
ℝⁿ near the box centre, with coordinates half of 1/3 and 2/3
alternately, at which a function H is positive, yields a rational
parameter t near 1/4 at which H is positive at P t. The proof is the
dyadic detection of the write-up (Lemma 7.15) along codes: rational
detection in n variables gives a rational point v in the box; twice v,
padded with the centres for the coordinates n, …, 2n, lies in the cells
of gist.RealCohesion.DigitCells; the curve at its codes converges to v
with modulus 2⁻ᴷ; and sequential hitting finds a code at which H is
positive. The codes stay within 2⁻ᵏ of 1/4. The points of ℝⁿ are
functions on Fin n, and index gives the coordinate of the curve.

\begin{code}

in-box : {n : ℕ} → ℕ → (Fin n → ℝ) → 𝓤₀ ̇
in-box {n} k y = (j : Fin n) → (ιₐ (box-centre (index j) ℚ- box-radius k) < y j)
                             × (y j < ιₐ (box-centre (index j) ℚ+ box-radius k))

margin : {n : ℕ} → ℕ → (Fin n → ℝ) → Fin n → ℝ
margin k y j = min (y j ℝ+ (ℝ- ιₐ (box-centre (index j) ℚ- box-radius k)))
                   (ιₐ (box-centre (index j) ℚ+ box-radius k) ℝ+ (ℝ- y j))

ιₐ-<-ιₐ⁻¹ : (a b : ℚ) → ιₐ a < ιₐ b → a < b
ιₐ-<-ιₐ⁻¹ a b = ∥∥-rec (ℚ<-is-prop a b) γ
 where
  γ : (Σ q ꞉ ℚ , (ιₐ a < q) × (q < ιₐ b)) → a < b
  γ (q , l , m) = ℚ<-trans a q b (ιₐ-upper⁻¹ a q l) (ιₐ-lower⁻¹ q b m)

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

 curve-detection
  : (n k : ℕ) (H : (Fin n → ℝ) → ℝ) (w₀ : Fin n → ℝ)
  → in-box k w₀
  → 0ℝ < H w₀
  → ∃ t ꞉ ℚ , close (pow½ k) t 1/4 × (0ℝ < H (λ j → P (dbl n) (index j) (ιₐ t)))
 curve-detection n k H w₀ box pos =
  ∥∥-rec ∃-is-prop γ (RD.rational-detection-in-dimension ν n h w₀
                        (rational-from-positive (h w₀) h-is-positive))
  where
   h : (Fin n → ℝ) → ℝ
   h y = min (H y) (Fin-min (margin k y))

   h-is-positive : 0ℝ < h w₀
   h-is-positive =
    positive-min (H w₀) (Fin-min (margin k w₀)) pos
     (Fin-min-is-positive (margin k w₀)
       (λ j → positive-min _ _
               (<-gives-positive-difference (w₀ j)
                 (ιₐ (box-centre (index j) ℚ- box-radius k))
                 (pr₁ (box j)))
               (<-gives-positive-difference
                 (ιₐ (box-centre (index j) ℚ+ box-radius k)) (w₀ j)
                 (pr₂ (box j)))))

   γ : (Σ v ꞉ (Fin n → ℚ) , 0ℚ < h (λ j → ιₐ (v j)))
     → ∃ t ꞉ ℚ ,
         close (pow½ k) t 1/4 × (0ℝ < H (λ j → P (dbl n) (index j) (ιₐ t)))
   γ (v , o) = ∥∥-functor δ
                (positive-sequential-hitting-for-functionals ν (Fin n) H
                  (λ j → ιₐ (v j)) z c
                  (pr₁ (positive-min⁻¹ _ _ o')))
    where
     o' : 0ℝ < h (λ j → ιₐ (v j))
     o' = positive-from-rational (h (λ j → ιₐ (v j))) o

     v-in-box : (j : Fin n) → (box-centre (index j) ℚ- box-radius k < v j)
                            × (v j < box-centre (index j) ℚ+ box-radius k)
     v-in-box j = ιₐ-<-ιₐ⁻¹ _ _ (<-from-difference _ _ (pr₁ I)) ,
                  ιₐ-<-ιₐ⁻¹ _ _ (<-from-difference _ _ (pr₂ I))
      where
       I = positive-min⁻¹ _ _ (positive-Fin-min (margin k (λ j' → ιₐ (v j')))
                                (pr₂ (positive-min⁻¹ _ _ o')) j)

     w : ℕ → ℚ
     w = extend n (λ j → v j ℚ+ v j) (λ i → centre-of (alt i))

     doubled : (j : Fin n) → cell k (alt (index j)) (v j ℚ+ v j)
     doubled j =
      doubled-cell k (index j) (v j) (pr₁ (v-in-box j)) (pr₂ (v-in-box j))

     cells : (i : ℕ) → i <ℕ succ (dbl n) → cell k (alt i) (w i)
     cells i _ =
      extend-property n (λ j → v j ℚ+ v j) (λ i' → centre-of (alt i'))
                  (λ i' x → cell k (alt i') x) doubled
                  (λ i' _ → centre-is-in-its-cells k (alt i')) i

     t : ℕ → ℚ
     t K = code (succ (dbl n)) (K +ℕ k) w

     z : ℕ → Fin n → ℝ
     z K j = P (dbl n) (index j) (ιₐ (t K))

     c : (K : ℕ) → z K is-within-2⁻ K of (λ j → ιₐ (v j))
     c K j = starter-bounds-from-within K (z K j) (ιₐ (v j))
              (within-weaken (ρ (K +ℕ k)) (⟨1/2⟩^ K) (z K j) (ιₐ (v j))
                (ℚ≤-trans (ρ (K +ℕ k)) (ρ K) (⟨1/2⟩^ K)
                  (ρ-antitone K (K +ℕ k) (≤-+ K k))
                  (ρ-is-below-power K))
                (transport (λ y → within (ρ (K +ℕ k)) y (ιₐ (v j)))
                  (I ⁻¹)
                  (transport (λ a → within (ρ (K +ℕ k))
                    (ιₐ (DS (digits (w (index j))) (K +ℕ k))) (ιₐ a))
                    (ap half (extend-at n (λ j' → v j' ℚ+ v j')
                               (λ i → centre-of (alt i)) j)
                     ∙ half-of-double (v j))
                    (within-of-bounds (DS (digits (w (index j))) (K +ℕ k))
                      (half (w (index j)))
                      (ρ (K +ℕ k)) (pow½-is-nonneg (succ (K +ℕ k)))
                      (pr₁ II) (pr₂ II)))))
      where
       I : z K j ＝ ιₐ (DS (digits (w (index j))) (K +ℕ k))
       I = P-at-code (dbl n) (K +ℕ k) w (index j)
            (below-dbl n (index j) (index-bound j))

       II = DS-bounds (K +ℕ k) (w (index j))
             (cell-in-𝕁 k (alt (index j)) (w (index j))
               (cells (index j) (below-dbl n (index j) (index-bound j))))

     δ : (Σ K ꞉ ℕ , 0ℝ < H (z K))
       → Σ t' ꞉ ℚ ,
           close (pow½ k) t' 1/4 × (0ℝ < H (λ j → P (dbl n) (index j) (ιₐ t')))
     δ (K , p) =
      t K , code-is-near-the-centre n (K +ℕ k) k w (≤-+' K k) cells , p

\end{code}
