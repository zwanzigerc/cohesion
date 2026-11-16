Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The rational arithmetic of GPT-6 Astra's digit-interleaving curve, for
gate G24 of Claude Fable 5.2's second addendum [1]: the n-variable form
of Shulman's Theorem 11.5 from Axiom R♭ alone, Theorem 7.17 of the
write-up [2], whose proof uses the curve of its Lemma 7.16.

The curve reads ternary digits with the two branches of the shift
S t = 3t - 2 d(t): on [0, 1/3] it is t ↦ 3t, on [2/3, 1] it is
t ↦ 3t - 2. Their inverses are the maps L ₀ s = s/3 and L ₁ s = s/3 + 2/3
of this module, and a point L b s with s in [0, 1] has reading b and
shift s. A word of bits is read block by block, each block of length
m: the l-th block holds the l-th binary digits of the m coordinates.
This module provides:

 * the maps L, their values in the unit interval, and the rational
   identities behind the readings of the real curve;

 * contraction: points whose first k blocks agree are within 2⁻ᵏ of
   each other;

 * binary digits by the map T s = 2s - b(s), and weighted digit sums
   with the weights 2⁻⁽ᵏ⁺²⁾ of gist.RealCohesion.PositiveTerms, which
   approximate half a number in [0, 1) to within 2⁻⁽ᴺ⁺¹⁾;

 * the code of a rational vector w at level K: the point whose blocks
   hold the first K binary digits of the coordinates of w, then zeros;

 * the centre 1/4, whose readings alternate 0, 1, 0, 1, …, with orbit
   1/4, 3/4; and the cells around 1/3 and 2/3, whose points have the
   alternating binary digits of 1/3 and 2/3 for as many places as the
   level of the cell.

The centre differs from Astra's 1/(3ⁿ + 1): with blocks of odd length
m, the readings 0, 1, 0, 1, … of 1/4 put the alternating digits of 1/3
or 2/3 in every coordinate, as Astra's centre puts those of 1/3. So the
curve is used with m = 2n + 1 coordinates, of which the first n matter,
and nothing about the centre depends on n.

This module has no parameters, so that rationals computed by its
functions are compared quickly inside real numbers
(gist.RealCohesion.RationalGrid explains why).

[1] Claude Fable 5.2. Second addendum to the formalization plan,
    revision 4 of 12 November 2026, §3, G24.
    references/F13b-second-addendum-rev4-as-amended.md

[2] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revision of 12 November 2026, Lemma 7.16
    and Theorem 7.17.
    references/C04-write-up-2026-11-12.tex

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.DigitCodes where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import MLTT.List using (List ; [] ; _∷_ ; length)
open import MLTT.Two-Properties using (complement)
open import UF.Base using (ap₂ ; transport₂)
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition
open import Rationals.Negation
open import Rationals.Multiplication
open import gist.RealCohesion.RationalArithmetic
 using (half ; halves-add-up ; half-of-double ; two ; half-is-nonneg ;
         half-is-at-most ;
        half-is-monotone ; half-is-strictly-monotone ; add-difference ;
         minus-zero ; plus-minus ;
        difference-of-translates ; 1/2≤1 ; 0≤1/2)

\end{code}

Bits, weights, alternation and odd block lengths.

\begin{code}

bit : 𝟚 → ℚ
bit ₀ = 0ℚ
bit ₁ = 1ℚ

scaled : 𝟚 → ℚ → ℚ
scaled ₀ p = 0ℚ
scaled ₁ p = p

complement-twice : (b : 𝟚) → complement (complement b) ＝ b
complement-twice ₀ = refl
complement-twice ₁ = refl

altfrom : 𝟚 → ℕ → 𝟚
altfrom b 0        = b
altfrom b (succ k) = altfrom (complement b) k

alt : ℕ → 𝟚
alt = altfrom ₀

altfrom-complement : (b : 𝟚) (k : ℕ)
                   → altfrom (complement b) k ＝ complement (altfrom b k)
altfrom-complement b 0        = refl
altfrom-complement b (succ k) = altfrom-complement (complement b) k

altfrom-sum : (b : 𝟚) (j k : ℕ) → altfrom b (j +ℕ k) ＝ altfrom (altfrom b j) k
altfrom-sum b j 0        = refl
altfrom-sum b j (succ k) = altfrom-sum (complement b) j k
                         ∙ ap (λ c → altfrom c k) (altfrom-complement b j)

alt-swap : (i q : ℕ) → altfrom (alt i) q ＝ altfrom (alt q) i
alt-swap i q =
 altfrom-sum ₀ i q ⁻¹ ∙ ap alt (addition-commutativity i q) ∙ altfrom-sum ₀ q i

dbl : ℕ → ℕ
dbl 0        = 0
dbl (succ n) = succ (succ (dbl n))

altfrom-dbl : (b : 𝟚) (n : ℕ) → altfrom b (dbl n) ＝ b
altfrom-dbl b 0        = refl
altfrom-dbl b (succ n) =
 ap (λ c → altfrom c (dbl n)) (complement-twice b) ∙ altfrom-dbl b n

below-dbl : (n i : ℕ) → i <ℕ n → i <ℕ succ (dbl n)
below-dbl 0        i        l = 𝟘-elim l
below-dbl (succ n) 0        l = ⋆
below-dbl (succ n) (succ i) l =
 ≤-trans (succ i) (succ (dbl n)) (succ (succ (dbl n)))
                                 (below-dbl n i l) (≤-succ (succ (dbl n)))

\end{code}

The two branches of the ternary shift, and the unit interval.

\begin{code}

third : ℚ → ℚ
third s = s * 1/3

triple : ℚ → ℚ
triple s = s + s + s

L : 𝟚 → ℚ → ℚ
L ₀ s = third s
L ₁ s = third s + 2/3

_∈𝕀 : ℚ → 𝓤₀ ̇
s ∈𝕀 = (0ℚ ≤ s) × (s ≤ 1ℚ)

abstract
 1/3+1/3' : 1/3 + 1/3 ＝ 2/3
 1/3+1/3' = refl

 2/3+1/3' : 2/3 + 1/3 ＝ 1ℚ
 2/3+1/3' = refl

 1/3+2/3' : 1/3 + 2/3 ＝ 1ℚ
 1/3+2/3' = refl

 triple-two-thirds : triple 2/3 ＝ two
 triple-two-thirds = refl

 one-plus-one : 1ℚ + 1ℚ ＝ two
 one-plus-one = refl

 two-minus-one : two - 1ℚ ＝ 1ℚ
 two-minus-one = refl

 third-of-one : third 1ℚ ＝ 1/3
 third-of-one = refl

 0≤1/3 : 0ℚ ≤ 1/3
 0≤1/3 = ℚ<-coarser-than-≤ 0ℚ 1/3 0<1/3

 0≤2/3 : 0ℚ ≤ 2/3
 0≤2/3 = 2 , refl

 1/3≤1/2 : 1/3 ≤ 1/2
 1/3≤1/2 = 1 , refl

 1/3≤1 : 1/3 ≤ 1ℚ
 1/3≤1 = 2 , refl

triple-third : (s : ℚ) → triple (third s) ＝ s
triple-third s =
 ap (_+ third s) (ℚ-distributivity s 1/3 1/3 ⁻¹ ∙ ap (s *_) 1/3+1/3')
               ∙ ℚ-distributivity s 2/3 1/3 ⁻¹
               ∙ ap (s *_) 2/3+1/3'
               ∙ ℚ-mult-right-id s

interchange : (a b c d : ℚ) → (a + b) + (c + d) ＝ (a + c) + (b + d)
interchange a b c d = ℚ+-assoc a b (c + d)
                    ∙ ap (a +_) (ℚ+-assoc b c d ⁻¹ ∙ ap (_+ d) (ℚ+-comm b c)
                                 ∙ ℚ+-assoc c b d)
                    ∙ ℚ+-assoc a c (b + d) ⁻¹

triple-sum : (a b : ℚ) → triple (a + b) ＝ triple a + triple b
triple-sum a b =
 ap (_+ (a + b)) (interchange a b a b) ∙ interchange (a + a) (b + b) a b

triple-L₁ : (s : ℚ) → triple (L ₁ s) ＝ s + two
triple-L₁ s =
 triple-sum (third s) 2/3 ∙ ap₂ _+_ (triple-third s) triple-two-thirds

\end{code}

The readings of the real curve at L b s: the argument 3t - 1 of its
clamps is at most 0 for b = ₀ and at least 1 for b = ₁, and the shift
3t - 2·b returns s.

\begin{code}

argument-of-L₀ : (s : ℚ) → s ≤ 1ℚ → triple (L ₀ s) - 1ℚ ≤ 0ℚ
argument-of-L₀ s l =
 transport₂ _≤_ (ap (_- 1ℚ) (triple-third s ⁻¹)) (ℚ-inverse-sum-to-zero 1ℚ)
                      (ℚ≤-addition-preserves-order s 1ℚ (- 1ℚ) l)

argument-of-L₁ : (s : ℚ) → 0ℚ ≤ s → 1ℚ ≤ triple (L ₁ s) - 1ℚ
argument-of-L₁ s l = transport₂ _≤_ (ℚ-zero-left-neutral 1ℚ) I
                      (ℚ≤-addition-preserves-order 0ℚ s 1ℚ l)
 where
  I : s + 1ℚ ＝ triple (L ₁ s) - 1ℚ
  I = ap (s +_) two-minus-one ⁻¹ ∙ ℚ+-assoc s two (- 1ℚ) ⁻¹
      ∙ ap (_- 1ℚ) (triple-L₁ s ⁻¹)

shift-of-L : (b : 𝟚) (s : ℚ) → triple (L b s) - (bit b + bit b) ＝ s
shift-of-L ₀ s = ap (triple (L ₀ s) +_) (ap -_ (ℚ-zero-left-neutral 0ℚ))
                 ∙ minus-zero (triple (L ₀ s))
               ∙ triple-third s
shift-of-L ₁ s =
 ap (λ c → triple (L ₁ s) - c) one-plus-one ∙ ap (_- two) (triple-L₁ s)
               ∙ plus-minus s two

third-bounds : (s : ℚ) → s ∈𝕀 → (0ℚ ≤ third s) × (third s ≤ 1/3)
third-bounds s (l , m) = ℚ≤-pos-multiplication-preserves-order s 1/3 l 0≤1/3 ,
                         transport (third s ≤_) (ℚ-mult-left-id 1/3)
                          (ℚ≤-pos-multiplication-preserves-order' s 1ℚ 1/3 m
                            0≤1/3)

L-in-𝕀 : (b : 𝟚) (s : ℚ) → s ∈𝕀 → L b s ∈𝕀
L-in-𝕀 ₀ s i = pr₁ (third-bounds s i) ,
                ℚ≤-trans (third s) 1/3 1ℚ (pr₂ (third-bounds s i)) 1/3≤1
L-in-𝕀 ₁ s i = ℚ≤-trans 0ℚ 2/3 (third s + 2/3) 0≤2/3
                (transport (_≤ third s + 2/3) (ℚ-zero-left-neutral 2/3)
                  (ℚ≤-addition-preserves-order 0ℚ (third s) 2/3
                    (pr₁ (third-bounds s i)))) ,
               transport (third s + 2/3 ≤_) 1/3+2/3'
                (ℚ≤-addition-preserves-order (third s) 1/3 2/3
                  (pr₂ (third-bounds s i)))

zero-in-𝕀 : 0ℚ ∈𝕀
zero-in-𝕀 = ℚ≤-refl 0ℚ , ℚ<-coarser-than-≤ 0ℚ 1ℚ 0<1

L₀-of-zero : L ₀ 0ℚ ＝ 0ℚ
L₀-of-zero = ℚ-zero-left-is-zero 1/3

\end{code}

Blocks. A list of bits acts by the composite of the maps L, the first
bit outermost.

\begin{code}

Lblock : List 𝟚 → ℚ → ℚ
Lblock []       y = y
Lblock (b ∷ bs) y = L b (Lblock bs y)

Lblock-in-𝕀 : (bs : List 𝟚) (y : ℚ) → y ∈𝕀 → Lblock bs y ∈𝕀
Lblock-in-𝕀 []       y i = i
Lblock-in-𝕀 (b ∷ bs) y i = L-in-𝕀 b (Lblock bs y) (Lblock-in-𝕀 bs y i)

letter : List 𝟚 → ℕ → 𝟚
letter []       j        = ₀
letter (b ∷ bs) 0        = b
letter (b ∷ bs) (succ j) = letter bs j

drop : ℕ → List 𝟚 → List 𝟚
drop 0        bs       = bs
drop (succ j) []       = []
drop (succ j) (b ∷ bs) = drop j bs

Lblock-drop : (bs : List 𝟚) (y : ℚ) (i : ℕ) → i <ℕ length bs
            → Lblock (drop i bs) y
            ＝ L (letter bs i) (Lblock (drop (succ i) bs) y)
Lblock-drop []       y i        l = 𝟘-elim l
Lblock-drop (b ∷ bs) y 0        l = refl
Lblock-drop (b ∷ bs) y (succ i) l = Lblock-drop bs y i l

blockOf : ℕ → (ℕ → 𝟚) → List 𝟚
blockOf 0        f = []
blockOf (succ m) f = f 0 ∷ blockOf m (λ i → f (succ i))

length-of-blockOf : (m : ℕ) (f : ℕ → 𝟚) → length (blockOf m f) ＝ m
length-of-blockOf 0        f = refl
length-of-blockOf (succ m) f = ap succ (length-of-blockOf m (λ i → f (succ i)))

letter-of-blockOf : (m : ℕ) (f : ℕ → 𝟚) (i : ℕ) → i <ℕ m
                  → letter (blockOf m f) i ＝ f i
letter-of-blockOf 0        f i        l = 𝟘-elim l
letter-of-blockOf (succ m) f 0        l = refl
letter-of-blockOf (succ m) f (succ i) l =
 letter-of-blockOf m (λ j → f (succ j)) i l

blockOf-ext : (m : ℕ) (f g : ℕ → 𝟚) → ((i : ℕ) → i <ℕ m → f i ＝ g i)
            → blockOf m f ＝ blockOf m g
blockOf-ext 0        f g e = refl
blockOf-ext (succ m) f g e = ap₂ _∷_ (e 0 ⋆)
                              (blockOf-ext m (λ i → f (succ i))
                                (λ i → g (succ i)) (λ i → e (succ i)))

Lblock-of-zeros : (m : ℕ) → Lblock (blockOf m (λ _ → ₀)) 0ℚ ＝ 0ℚ
Lblock-of-zeros 0        = refl
Lblock-of-zeros (succ m) = ap third (Lblock-of-zeros m) ∙ L₀-of-zero

\end{code}

Contraction. Each map L shrinks distances by 3, so a nonempty block at
least halves them.

\begin{code}

close : ℚ → ℚ → ℚ → 𝓤₀ ̇
close e x y = (x - y ≤ e) × (y - x ≤ e)

third-of-difference : (x y : ℚ) → third x - third y ＝ third (x - y)
third-of-difference x y = ap (third x +_) (ℚ-negation-dist-over-mult y 1/3 ⁻¹)
                        ∙ ℚ-distributivity' 1/3 x (- y) ⁻¹

L-difference : (b : 𝟚) (x y : ℚ) → L b x - L b y ＝ third (x - y)
L-difference ₀ x y = third-of-difference x y
L-difference ₁ x y =
 difference-of-translates (third x) (third y) 2/3 ∙ third-of-difference x y

third-is-at-most-half : (e : ℚ) → 0ℚ ≤ e → third e ≤ half e
third-is-at-most-half e l = transport₂ _≤_ (ℚ*-comm 1/3 e) (ℚ*-comm 1/2 e)
                             (ℚ≤-pos-multiplication-preserves-order' 1/3 1/2 e
                               1/3≤1/2 l)

third-is-monotone : (x y : ℚ) → x ≤ y → third x ≤ third y
third-is-monotone x y l = ℚ≤-pos-multiplication-preserves-order' x y 1/3 l 0≤1/3

L-contracts : (b : 𝟚) (e x y : ℚ) → 0ℚ ≤ e → close e x y
            → close (half e) (L b x) (L b y)
L-contracts b e x y l (m , m') =
 transport (_≤ half e) (L-difference b x y ⁻¹)
  (ℚ≤-trans (third (x - y)) (third e) (half e) (third-is-monotone (x - y) e m)
    (third-is-at-most-half e l)) ,
 transport (_≤ half e) (L-difference b y x ⁻¹)
  (ℚ≤-trans (third (y - x)) (third e) (half e) (third-is-monotone (y - x) e m')
    (third-is-at-most-half e l))

close-weaken : (e e' x y : ℚ) → e ≤ e' → close e x y → close e' x y
close-weaken e e' x y k (m , m') =
 ℚ≤-trans (x - y) e e' m k , ℚ≤-trans (y - x) e e' m' k

Lblock-preserves : (bs : List 𝟚) (e x y : ℚ) → 0ℚ ≤ e → close e x y
                 → close e (Lblock bs x) (Lblock bs y)
Lblock-preserves []       e x y l c = c
Lblock-preserves (b ∷ bs) e x y l c =
 close-weaken (half e) e (L b (Lblock bs x)) (L b (Lblock bs y))
  (half-is-at-most e l)
  (L-contracts b e (Lblock bs x) (Lblock bs y) l
    (Lblock-preserves bs e x y l c))

Lblock-contracts : (b : 𝟚) (bs : List 𝟚) (e x y : ℚ) → 0ℚ ≤ e → close e x y
                 → close (half e) (Lblock (b ∷ bs) x) (Lblock (b ∷ bs) y)
Lblock-contracts b bs e x y l c =
 L-contracts b e (Lblock bs x) (Lblock bs y) l (Lblock-preserves bs e x y l c)

points-of-𝕀-are-close : (x y : ℚ) → x ∈𝕀 → y ∈𝕀 → close 1ℚ x y
points-of-𝕀-are-close x y (l , m) (l' , m') = I x y m l' , I y x m' l
 where
  I : (a b : ℚ) → a ≤ 1ℚ → 0ℚ ≤ b → a - b ≤ 1ℚ
  I a b k k' = transport (a - b ≤_) (minus-zero 1ℚ)
                (ℚ≤-adding a 1ℚ (- b) (- 0ℚ) k (ℚ≤-swap 0ℚ b k'))

\end{code}

Binary digits: the first digit of s in [0, 1) is ₀ if s < 1/2 and ₁
otherwise, and T s = 2s - digit is the rest.

\begin{code}

β-of : (s : ℚ) → (s < 1/2) ∔ (1/2 ≤ s) → 𝟚
β-of s (inl _) = ₀
β-of s (inr _) = ₁

β : ℚ → 𝟚
β s = β-of s (ℚ-dichotomous' s 1/2)

β-small : (s : ℚ) → s < 1/2 → β s ＝ ₀
β-small s l = γ (ℚ-dichotomous' s 1/2)
 where
  γ : (c : (s < 1/2) ∔ (1/2 ≤ s)) → β-of s c ＝ ₀
  γ (inl _) = refl
  γ (inr k) = 𝟘-elim (ℚ<-irrefl s (ℚ<-≤-trans s 1/2 s l k))

β-large : (s : ℚ) → 1/2 ≤ s → β s ＝ ₁
β-large s k = γ (ℚ-dichotomous' s 1/2)
 where
  γ : (c : (s < 1/2) ∔ (1/2 ≤ s)) → β-of s c ＝ ₁
  γ (inl l) = 𝟘-elim (ℚ<-irrefl s (ℚ<-≤-trans s 1/2 s l k))
  γ (inr _) = refl

T : ℚ → ℚ
T s = (s + s) - bit (β s)

reading : (s : ℚ) → s ＝ half (bit (β s) + T s)
reading s =
 half-of-double s ⁻¹ ∙ ap half (add-difference (bit (β s)) (s + s) ⁻¹)

_∈𝕁 : ℚ → 𝓤₀ ̇
s ∈𝕁 = (0ℚ ≤ s) × (s < 1ℚ)

T-in-𝕁 : (s : ℚ) → s ∈𝕁 → T s ∈𝕁
T-in-𝕁 s (l , m) = γ (ℚ-dichotomous' s 1/2)
 where
  P : 𝟚 → 𝓤₀ ̇
  P c = ((s + s) - bit c) ∈𝕁

  γ : (s < 1/2) ∔ (1/2 ≤ s) → T s ∈𝕁
  γ (inl k) = transport P (β-small s k ⁻¹)
               (transport _∈𝕁 (minus-zero (s + s) ⁻¹)
                 (transport (_≤ s + s) (ℚ-zero-left-neutral 0ℚ)
                   (ℚ≤-adding 0ℚ s 0ℚ s l l) ,
                  transport (s + s <_) 1/2+1/2 (ℚ<-adding s 1/2 s 1/2 k k)))
  γ (inr k) = transport P (β-large s k ⁻¹)
               (ℚ≤-difference-positive 1ℚ (s + s)
                 (transport (_≤ s + s) 1/2+1/2 (ℚ≤-adding 1/2 s 1/2 s k k)) ,
                transport ((s + s) - 1ℚ <_) (plus-minus 1ℚ 1ℚ)
                 (ℚ<-addition-preserves-order (s + s) (1ℚ + 1ℚ) (- 1ℚ)
                   (ℚ<-adding s 1ℚ s 1ℚ m m)))

T^ : ℕ → ℚ → ℚ
T^ 0        s = s
T^ (succ k) s = T^ k (T s)

digits : ℚ → ℕ → 𝟚
digits s k = β (T^ k s)

\end{code}

Weighted digit sums. The digit of place k has weight
ρ' (succ k) = 2⁻⁽ᵏ⁺²⁾, as the terms of gist.RealCohesion.PositiveTerms;
ρ' is ρ of gist.RealCohesion.RealLimits, by definition. The sum of the
first N digits of s in [0, 1) is within 2⁻⁽ᴺ⁺¹⁾ below s/2.

\begin{code}

ρ' : ℕ → ℚ
ρ' n = rec 1/2 (_* 1/2) n

DS : (ℕ → 𝟚) → ℕ → ℚ
DS f 0        = 0ℚ
DS f (succ N) = DS f N + scaled (f N) (ρ' (succ N))

half-of-zero : half 0ℚ ＝ 0ℚ
half-of-zero = ℚ-zero-left-is-zero 1/2

half-of-sum : (a b : ℚ) → half (a + b) ＝ half a + half b
half-of-sum a b = ℚ-distributivity' 1/2 a b

half-of-scaled : (b : 𝟚) (p : ℚ) → half (scaled b p) ＝ scaled b (half p)
half-of-scaled ₀ p = half-of-zero
half-of-scaled ₁ p = refl

DS-front : (f : ℕ → 𝟚) (N : ℕ)
         → DS f (succ N) ＝ scaled (f 0) (ρ' 1) + half (DS (λ k → f (succ k)) N)
DS-front f 0        = ℚ-zero-left-neutral (scaled (f 0) (ρ' 1))
                    ∙ ℚ-zero-right-neutral (scaled (f 0) (ρ' 1)) ⁻¹
                    ∙ ap (scaled (f 0) (ρ' 1) +_) (half-of-zero ⁻¹)
DS-front f (succ N) =
   ap (_+ scaled (f (succ N)) (ρ' (succ (succ N)))) (DS-front f N)
 ∙ ℚ+-assoc (scaled (f 0) (ρ' 1)) (half (DS (λ k → f (succ k)) N))
            (scaled (f (succ N)) (ρ' (succ (succ N))))
 ∙ ap (scaled (f 0) (ρ' 1) +_)
      (ap (half (DS (λ k → f (succ k)) N) +_)
        (half-of-scaled (f (succ N)) (ρ' (succ N)) ⁻¹)
       ∙ half-of-sum (DS (λ k → f (succ k)) N)
          (scaled (f (succ N)) (ρ' (succ N))) ⁻¹)

half-of-half-of-bit : (b : 𝟚) → half (half (bit b)) ＝ scaled b (ρ' 1)
half-of-half-of-bit ₀ = ap half half-of-zero ∙ half-of-zero
half-of-half-of-bit ₁ = ap half (ℚ-mult-left-id 1/2)

add-left-strict : (a x y : ℚ) → x < y → a + x < a + y
add-left-strict a x y l = transport₂ _<_ (ℚ+-comm x a) (ℚ+-comm y a)
                           (ℚ<-addition-preserves-order x y a l)

DS-bounds : (N : ℕ) (s : ℚ) → s ∈𝕁
          → (DS (digits s) N ≤ half s) × (half s < DS (digits s) N + ρ' N)
DS-bounds 0        s (l , m) =
 half-is-nonneg s l ,
 transport (half s <_) (ℚ-mult-left-id 1/2 ∙ ℚ-zero-left-neutral 1/2 ⁻¹)
  (half-is-strictly-monotone s 1ℚ m)
DS-bounds (succ N) s (l , m) = lower , upper
 where
  A D : ℚ
  A = scaled (β s) (ρ' 1)
  D = DS (digits (T s)) N

  IH : (D ≤ half (T s)) × (half (T s) < D + ρ' N)
  IH = DS-bounds N (T s) (T-in-𝕁 s (l , m))

  e : DS (digits s) (succ N) ＝ A + half D
  e = DS-front (digits s) N

  hs : half s ＝ A + half (half (T s))
  hs = ap half (reading s)
     ∙ ap half (half-of-sum (bit (β s)) (T s))
     ∙ half-of-sum (half (bit (β s))) (half (T s))
     ∙ ap (_+ half (half (T s))) (half-of-half-of-bit (β s))

  lower : DS (digits s) (succ N) ≤ half s
  lower = transport₂ _≤_ (e ⁻¹) (hs ⁻¹)
           (ℚ≤-adding A A (half D) (half (half (T s))) (ℚ≤-refl A)
             (half-is-monotone D (half (T s)) (pr₁ IH)))

  upper : half s < DS (digits s) (succ N) + ρ' (succ N)
  upper = transport₂ _<_ (hs ⁻¹) II
           (add-left-strict A (half (half (T s))) (half (D + ρ' N))
             (half-is-strictly-monotone (half (T s)) (D + ρ' N) (pr₂ IH)))
   where
    II : A + half (D + ρ' N) ＝ DS (digits s) (succ N) + ρ' (succ N)
    II = ap (A +_) (half-of-sum D (ρ' N)) ∙ ℚ+-assoc A (half D) (ρ' (succ N)) ⁻¹
       ∙ ap (_+ ρ' (succ N)) (e ⁻¹)

\end{code}

Codes. The code of w at level K, with blocks of length m, is the point
whose q-th block holds the q-th binary digits of w 0, …, w (m - 1) for
q < K, and zeros after. code-point m K w q is the point reached after
q blocks, and code-orbit is its block orbit.

\begin{code}

dig : ℕ → (ℕ → ℚ) → ℕ → ℕ → 𝟚
dig 0        w q        i = ₀
dig (succ K) w 0        i = β (w i)
dig (succ K) w (succ q) i = dig K (λ j → T (w j)) q i

dig-is-digits : (K : ℕ) (w : ℕ → ℚ) (q i : ℕ) → q <ℕ K
              → dig K w q i ＝ digits (w i) q
dig-is-digits 0        w q        i l = 𝟘-elim l
dig-is-digits (succ K) w 0        i l = refl
dig-is-digits (succ K) w (succ q) i l = dig-is-digits K (λ j → T (w j)) q i l

dig-beyond : (K : ℕ) (w : ℕ → ℚ) (q i : ℕ) → K ≤ℕ q → dig K w q i ＝ ₀
dig-beyond 0        w q        i l = refl
dig-beyond (succ K) w 0        i l = 𝟘-elim l
dig-beyond (succ K) w (succ q) i l = dig-beyond K (λ j → T (w j)) q i l

code-point : ℕ → ℕ → (ℕ → ℚ) → ℕ → ℚ
code-point m 0        w q        = 0ℚ
code-point m (succ K) w 0        = Lblock (blockOf m (λ i → β (w i)))
                                    (code-point m K (λ j → T (w j)) 0)
code-point m (succ K) w (succ q) = code-point m K (λ j → T (w j)) q

code-orbit : (m K : ℕ) (w : ℕ → ℚ) (q : ℕ)
           → code-point m K w q
           ＝ Lblock (blockOf m (λ i → dig K w q i)) (code-point m K w (succ q))
code-orbit m 0        w q        = Lblock-of-zeros m ⁻¹
code-orbit m (succ K) w 0        = refl
code-orbit m (succ K) w (succ q) = code-orbit m K (λ j → T (w j)) q

code-point-in-𝕀 : (m K : ℕ) (w : ℕ → ℚ) (q : ℕ) → code-point m K w q ∈𝕀
code-point-in-𝕀 m 0        w q        = zero-in-𝕀
code-point-in-𝕀 m (succ K) w 0        = Lblock-in-𝕀 (blockOf m (λ i → β (w i)))
                                         (code-point m K (λ j → T (w j)) 0)
                                         (code-point-in-𝕀 m K (λ j → T (w j)) 0)
code-point-in-𝕀 m (succ K) w (succ q) = code-point-in-𝕀 m K (λ j → T (w j)) q

code : ℕ → ℕ → (ℕ → ℚ) → ℚ
code m K w = code-point m K w 0

\end{code}

The centre 1/4: its readings alternate, its orbit is 1/4, 3/4, and an
alternating block of odd length returns to it.

\begin{code}

point : 𝟚 → ℚ
point ₀ = 1/4
point ₁ = 3/4

abstract
 point-orbit : (b : 𝟚) → L b (point (complement b)) ＝ point b
 point-orbit ₀ = refl
 point-orbit ₁ = refl

 point-in-𝕀 : (b : 𝟚) → point b ∈𝕀
 point-in-𝕀 ₀ = (1 , refl) , (3 , refl)
 point-in-𝕀 ₁ = (3 , refl) , (1 , refl)

alternating-block : (j : ℕ) (b : 𝟚)
                  → Lblock (blockOf j (altfrom b)) (point (altfrom b j))
                  ＝ point b
alternating-block 0        b = refl
alternating-block (succ j) b =
 ap (L b) (alternating-block j (complement b)) ∙ point-orbit b

centre-orbit : (n q : ℕ)
             → point (alt q)
             ＝ Lblock (blockOf (succ (dbl n)) (altfrom (alt q)))
                (point (alt (succ q)))
centre-orbit n q = alternating-block (succ (dbl n)) (alt q) ⁻¹
                 ∙ ap (λ c → Lblock (blockOf (succ (dbl n)) (altfrom (alt q)))
                              (point c)) I
 where
  I : altfrom (alt q) (succ (dbl n)) ＝ alt (succ q)
  I = altfrom-dbl (complement (alt q)) n ∙ altfrom-complement ₀ q ⁻¹

\end{code}

Two block orbits whose first k blocks agree are within 2⁻ᵏ.

\begin{code}

pow½ : ℕ → ℚ
pow½ 0        = 1ℚ
pow½ (succ k) = ρ' k

pow½-succ : (k : ℕ) → pow½ (succ k) ＝ half (pow½ k)
pow½-succ 0        = ℚ-mult-left-id 1/2 ⁻¹
pow½-succ (succ k) = refl

pow½-is-nonneg : (k : ℕ) → 0ℚ ≤ pow½ k
pow½-is-nonneg 0        = ℚ<-coarser-than-≤ 0ℚ 1ℚ 0<1
pow½-is-nonneg (succ k) = transport (0ℚ ≤_) (pow½-succ k ⁻¹)
                           (half-is-nonneg (pow½ k) (pow½-is-nonneg k))

module _ (m : ℕ)
         (z z' : ℕ → ℚ)
         (B B' : ℕ → ℕ → 𝟚)
         (z-in-𝕀 : (q : ℕ) → z q ∈𝕀)
         (z'-in-𝕀 : (q : ℕ) → z' q ∈𝕀)
         (z-orbit : (q : ℕ)
          → z q ＝ Lblock (blockOf (succ m) (B q)) (z (succ q)))
         (z'-orbit : (q : ℕ)
          → z' q ＝ Lblock (blockOf (succ m) (B' q)) (z' (succ q)))
       where

 orbits-are-close
  : (k j : ℕ)
  → ((q : ℕ) → q <ℕ k
     → blockOf (succ m) (B (j +ℕ q)) ＝ blockOf (succ m) (B' (j +ℕ q)))
  → close (pow½ k) (z j) (z' j)
 orbits-are-close 0        j a =
  points-of-𝕀-are-close (z j) (z' j) (z-in-𝕀 j) (z'-in-𝕀 j)
 orbits-are-close (succ k) j a =
  transport₂ (close (pow½ (succ k))) (z-orbit j ⁻¹) (I ∙ z'-orbit j ⁻¹)
   (transport (λ e → close e (Lblock (blockOf (succ m) (B j)) (z (succ j)))
                             (Lblock (blockOf (succ m) (B j)) (z' (succ j))))
              (pow½-succ k ⁻¹)
    (Lblock-contracts (B j 0) (blockOf m (λ i → B j (succ i))) (pow½ k)
      (z (succ j)) (z' (succ j)) (pow½-is-nonneg k) IH))
  where
   IH : close (pow½ k) (z (succ j)) (z' (succ j))
   IH = orbits-are-close k (succ j)
         (λ q l →
           transport (λ x → blockOf (succ m) (B x) ＝ blockOf (succ m) (B' x))
                   (succ-left j q ⁻¹) (a (succ q) l))

   I : Lblock (blockOf (succ m) (B j)) (z' (succ j))
     ＝ Lblock (blockOf (succ m) (B' j)) (z' (succ j))
   I = ap (λ bs → Lblock bs (z' (succ j))) (a 0 ⋆)

\end{code}
