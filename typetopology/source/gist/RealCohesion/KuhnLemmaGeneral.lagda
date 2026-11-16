Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (13 November UTC). See the AI disclosure in
gist.RealCohesion.index.

Kuhn's lemma in every dimension, the last item of gate G14 of Claude
Fable 5.2's second addendum, by Fable's route [1], revision 3, which
GPT-6 Astra audited and released on 13 November 2026 UTC: steps K1 to
K7. Step K0 and the general form of K2 are in
gist.RealCohesion.KuhnCounting.

    kuhn-lemma : funext 𝓤₀ 𝓤₀ → (n : ℕ) → Kuhn-Lemma n

Kuhn-Lemma is the statement of gist.RealCohesion.KuhnLemma, unchanged:
for N = p + 1 and a labelling ℓ of the grid {0, …, N}ⁿ with ℓ a i = 0
when aᵢ = 0 and ℓ a i = 1 when aᵢ = N, there is q with qᵢ ≤ p and, for
each i, two corners of the unit cube at q, given as data, at which the
bit i of ℓ is 0 and 1. The proof uses function extensionality, as the
proof for n = 2 does, and no other hypothesis.

 * K1, the reduced label (reduced). Each coordinate i of Fin n has a
   position: in dimension m + 1 the position of 𝟎 is m, and the
   position of suc i is its position in dimension m (position). So the
   coordinate that the induction of K6 removes, 𝟎, is examined last.
   The reduced label of a bit vector is the first position at which
   the bit is 1, and n if there is none. If it is the position of i,
   the bit at i is 1 (reduced-hit); if it is larger, the bit at i is 0
   (reduced-before); it is at most n (reduced-bound); and if the bit
   at 𝟎 is 1, it is the reduced label of the remaining bits, in
   dimension m, including the fallback value m (reduced-top).

 * Codes. A code is a base b and a rank function r, both functions
   from Fin n to ℕ; for k = 0, …, n its vertex k is the corner of the
   unit cube at b with the bits [r(i) < k] (vertex). Its labels are the
   reduced labels of ℓ at its n + 1 vertices (labels). door k is 1 if
   every value 0, …, n − 1 is the label of a vertex other than vertex k,
   and the code is complete if every value 0, …, n is a label. A code
   is valid (Valid) if b i ≤ p, r i < n and r is injective. Validity
   is decidable, and it enters the sums as a Boolean factor, so no
   proof of validity is counted.

 * K2 (doors-of-a-code): the sum of door k over k = 0, …, n is
   complete, for every code and every labelling. This is the case of
   door-count of gist.RealCohesion.KuhnCounting with S = 0, …, n − 1,
   since all labels are at most n.

 * K3 (valid-ranks-take-every-value): an injective rank function takes
   every value below n, by the pigeonhole principle.

 * K4 (module moves), in dimension n = m + 1. A flag is a code with an
   index k. It is good if its code is valid, k ≤ n, and it is not
   blocked: blocked at k = 0 means base p at the coordinate of rank 0,
   and blocked at k = n means base 0 at the coordinate of rank m. The
   move at k = 0 adds 1 to the base at the coordinate of rank 0, gives
   it rank m and lowers the other ranks by 1, with new index n; the
   move at k = n is its inverse; at 0 < k < n the move exchanges the
   ranks k − 1 and k. For a good flag the move gives a good flag
   (move-is-good), a different one (move-changes), with the same door
   (move-keeps-door), and the move at the new flag gives the old flag
   back (move-move). The vertex identities (vertex-up, vertex-swapped)
   hold pointwise and then by function extensionality.

 * K5 (module step): the cancellation lemma K0 for T, the move on good
   flags and the identity on the others, and the weight [good] · door,
   over the list of all flags (cancel). With K2, the sum of
   [valid] · [complete] over all codes is the sum of [valid] · door
   over the blocked flags.

 * K6 (module step): a blocked flag has no door unless its index is 0
   and the coordinate 𝟎 has base p and rank 0 (blocked-at-zero,
   blocked-at-top, by K1); this is where the order of the reduced
   label matters. These boundary flags correspond to all codes of
   dimension m (boundary-code: base p and rank 0 at 𝟎, the other ranks
   raised by 1). Vertex j + 1 of the flag is vertex j of the smaller
   code with the coordinate N put at 𝟎 (vertex-boundary), and by K1 (d)
   the door of the flag is the completeness of the smaller code for
   the labelling restricted to that face (door-boundary), which has the
   boundary conditions. The sums are reindexed by sum-fixed-at-𝟎 and
   sum-avoiding-zero (equation). So the number of valid complete codes
   is odd in every dimension (parity-is-one); in dimension 0 there is
   one code, and it is complete.

 * K7 (kuhn-lemma): a valid complete code, from the sum (sum-is-one);
   q = b. For the coordinate i with position j, the vertex with label
   j + 1 has bit 0 at i and the vertex with label j has bit 1 at i, by
   K1; their indices come from the list of labels. The vertices are
   corners by definition, so these are the witnesses of Kuhn-Lemma.

The route is that of John Harrison's proof, in the pinned Isabelle file
Brouwer_Fixpoint.thy [2], through Fable's note: reduced and its lemmas
(lines 1290–1321) for K1; kuhn_complete_lemma (327–412) for K2; the
locale kuhn_simplex (413–572) for K3; ksimplex_replace_0, _1 and _2
(817–862, and from lines 880, 985 and 1101) for K4; kuhn_simplex_lemma
(1245–1289) for K5; simplex_top_face, complete_face_top, kuhn_induction,
ksimplex_0 and kuhn_combinatorial (713–816, 1322–1486) for K6; and
kuhn_lemma (1487–1535) for K7. No Isabelle text is translated: sets of
simplices are codes here, the fact that a facet lies in two simplices
is replaced by the moves, Isabelle's cardinalities by sums modulo 2
over lists, and LEAST by a recursion on n.

[1] Claude Fable 5.2. Kuhn's lemma in every dimension: the finite
    route. Revision 3, 13 November 2026, audited by GPT-6 Astra.
    references/F10-kuhn-finite-route-rev3.md

[2] Brouwer_Fixpoint.thy of Isabelle/HOL (src/HOL/Analysis), at
    revision 87958a2e5f99606413f8c4f3af90935a5ac33110 of the Isabelle
    mirror, by John Harrison (from HOL Light), translated to
    Isabelle/HOL by Robert Himmelmann, with LCP. See
    ISABELLE-COPYRIGHT in this folder. Kuhn's lemma is due to Harold
    W. Kuhn, Some combinatorial lemmas in topology, IBM Journal of
    Research and Development 4(5), 518–524, 1960.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.KuhnLemmaGeneral where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import MLTT.List using (List ; [] ; _∷_ ; length ; map ; map-∘)
open import MLTT.Plus-Properties using (inl-lc ; inr-lc ; +disjoint)
open import MLTT.Two-Properties using (_⊕_ ; zero-is-not-one)
open import Fin.Type
open import Fin.Topology using (Fin-is-discrete)
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order
open import Naturals.Properties
 using (pred ; succ-lc ; positive-not-zero ; succ-no-fp)
open import Notation.Order
open import NotionsOfDecidability.Decidable using (×-preserves-decidability ;
                                                   →-preserves-decidability)
open import UF.Base using (ap₂)
open import UF.DiscreteAndSeparated using (is-discrete ; ℕ-is-discrete)
open import UF.FunExt
open import gist.RealCohesion.KuhnLemma
 using (corner ; bit ; Kuhn-Lemma ; xor-right-unit)
open import gist.RealCohesion.KuhnCounting

\end{code}

K1. Positions, the first position at which a bit is 1, and the reduced
label.

\begin{code}

position : (n : ℕ) → Fin n → ℕ
position 0        i       = 𝟘-elim i
position (succ m) (inr ⋆) = m
position (succ m) (inl i) = position m i

position-bound : (n : ℕ) (i : Fin n) → position n i < n
position-bound 0        i       = 𝟘-elim i
position-bound (succ m) (inr ⋆) = <-succ m
position-bound (succ m) (inl i) =
 <-trans (position m i) m (succ m) (position-bound m i) (<-succ m)

first-step : ℕ → 𝟙 {𝓤₀} ∔ ℕ → 𝟚 → 𝟙 {𝓤₀} ∔ ℕ
first-step m (inr j) b = inr j
first-step m (inl ⋆) ₀ = inl ⋆
first-step m (inl ⋆) ₁ = inr m

first : (n : ℕ) → (Fin n → 𝟚) → 𝟙 {𝓤₀} ∔ ℕ
first 0        c = inl ⋆
first (succ m) c = first-step m (first m (λ i → c (inl i))) (c (inr ⋆))

from-first : ℕ → 𝟙 {𝓤₀} ∔ ℕ → ℕ
from-first n (inl ⋆) = n
from-first n (inr j) = j

reduced : (n : ℕ) → (Fin n → 𝟚) → ℕ
reduced n c = from-first n (first n c)

first-bound : (n : ℕ) (c : Fin n → 𝟚) (j : ℕ) → first n c ＝ inr j → j < n
first-bound 0        c j ()
first-bound (succ m) c j e = γ (first m c') (c (inr ⋆)) refl e
 where
  c' : Fin m → 𝟚
  c' i = c (inl i)

  γ : (o : 𝟙 ∔ ℕ) (b : 𝟚) → first m c' ＝ o → first-step m o b ＝ inr j
    → j < succ m
  γ (inr j') b p r = transport (_< succ m) (inr-lc r)
                      (<-trans j' m (succ m) (first-bound m c' j' p) (<-succ m))
  γ (inl ⋆)  ₀ p ()
  γ (inl ⋆)  ₁ p r = transport (_< succ m) (inr-lc r) (<-succ m)

first-none : (n : ℕ) (c : Fin n → 𝟚) → first n c ＝ inl ⋆ → (i : Fin n) → c i ＝ ₀
first-none 0        c e i = 𝟘-elim i
first-none (succ m) c e i = γ (first m c') (c (inr ⋆)) refl refl e i
 where
  c' : Fin m → 𝟚
  c' i = c (inl i)

  γ : (o : 𝟙 ∔ ℕ) (b : 𝟚) → first m c' ＝ o → c (inr ⋆) ＝ b
    → first-step m o b ＝ inl ⋆ → (i : Fin (succ m)) → c i ＝ ₀
  γ (inr j') b p q () i
  γ (inl ⋆)  ₀ p q r (inr ⋆) = q
  γ (inl ⋆)  ₀ p q r (inl i) = first-none m c' p i
  γ (inl ⋆)  ₁ p q () i

first-hit : (n : ℕ) (c : Fin n → 𝟚) (j : ℕ) → first n c ＝ inr j
          → (i : Fin n) → position n i ＝ j → c i ＝ ₁
first-hit 0        c j e i = 𝟘-elim i
first-hit (succ m) c j e i = γ (first m c') (c (inr ⋆)) refl refl e i
 where
  c' : Fin m → 𝟚
  c' i = c (inl i)

  γ : (o : 𝟙 ∔ ℕ) (b : 𝟚) → first m c' ＝ o → c (inr ⋆) ＝ b
    → first-step m o b ＝ inr j → (i : Fin (succ m)) → position (succ m) i ＝ j
    → c i ＝ ₁
  γ (inr j') b p q r (inr ⋆) s = 𝟘-elim (not-less-than-itself m
                                   (transport (_< m) (inr-lc r ∙ s ⁻¹)
                                     (first-bound m c' j' p)))
  γ (inr j') b p q r (inl i) s = first-hit m c' j' p i (s ∙ inr-lc r ⁻¹)
  γ (inl ⋆)  ₀ p q () i s
  γ (inl ⋆)  ₁ p q r (inr ⋆) s = q
  γ (inl ⋆)  ₁ p q r (inl i) s = 𝟘-elim (not-less-than-itself m
                                   (transport (_< m) (s ∙ inr-lc r ⁻¹)
                                     (position-bound m i)))

first-before : (n : ℕ) (c : Fin n → 𝟚) (j : ℕ) → first n c ＝ inr j
             → (i : Fin n) → position n i < j → c i ＝ ₀
first-before 0        c j e i = 𝟘-elim i
first-before (succ m) c j e i = γ (first m c') (c (inr ⋆)) refl refl e i
 where
  c' : Fin m → 𝟚
  c' i = c (inl i)

  γ : (o : 𝟙 ∔ ℕ) (b : 𝟚) → first m c' ＝ o → c (inr ⋆) ＝ b
    → first-step m o b ＝ inr j → (i : Fin (succ m)) → position (succ m) i < j
    → c i ＝ ₀
  γ (inr j') b p q r (inr ⋆) s = 𝟘-elim (not-less-than-itself m
                                   (<-trans m j' m
                                     (transport (m <_) (inr-lc r ⁻¹) s)
                                     (first-bound m c' j' p)))
  γ (inr j') b p q r (inl i) s =
   first-before m c' j' p i (transport (position m i <_) (inr-lc r ⁻¹) s)
  γ (inl ⋆)  ₀ p q () i s
  γ (inl ⋆)  ₁ p q r (inr ⋆) s =
   𝟘-elim (not-less-than-itself m (transport (m <_) (inr-lc r ⁻¹) s))
  γ (inl ⋆)  ₁ p q r (inl i) s = first-none m c' p i

reduced-bound : (n : ℕ) (c : Fin n → 𝟚) → reduced n c ≤ n
reduced-bound n c = γ (first n c) refl
 where
  γ : (o : 𝟙 ∔ ℕ) → first n c ＝ o → from-first n o ≤ n
  γ (inl ⋆) _ = ≤-refl n
  γ (inr j) p = <-coarser-than-≤ j n (first-bound n c j p)

reduced-hit : (n : ℕ) (c : Fin n → 𝟚) (i : Fin n) → reduced n c ＝ position n i
            → c i ＝ ₁
reduced-hit n c i = γ (first n c) refl
 where
  γ : (o : 𝟙 ∔ ℕ) → first n c ＝ o → from-first n o ＝ position n i → c i ＝ ₁
  γ (inl ⋆) _ s = 𝟘-elim
   (not-less-than-itself n (transport (_< n) (s ⁻¹) (position-bound n i)))
  γ (inr j) p s = first-hit n c j p i (s ⁻¹)

reduced-before : (n : ℕ) (c : Fin n → 𝟚) (i : Fin n)
               → position n i < reduced n c → c i ＝ ₀
reduced-before n c i = γ (first n c) refl
 where
  γ : (o : 𝟙 ∔ ℕ) → first n c ＝ o → position n i < from-first n o → c i ＝ ₀
  γ (inl ⋆) p s = first-none n c p i
  γ (inr j) p s = first-before n c j p i s

reduced-top : (m : ℕ) (c : Fin (succ m) → 𝟚)
            → c (inr ⋆) ＝ ₁ → reduced (succ m) c ＝ reduced m (λ i → c (inl i))
reduced-top m c = γ (first m (λ i → c (inl i))) (c (inr ⋆))
 where
  γ : (o : 𝟙 ∔ ℕ) (b : 𝟚) → b ＝ ₁
    → from-first (succ m) (first-step m o b) ＝ from-first m o
  γ (inr j) b q = refl
  γ (inl ⋆) ₀ q = 𝟘-elim (zero-is-not-one q)
  γ (inl ⋆) ₁ q = refl

\end{code}

The two consequences that Fable's note lists as K1 (a) and (b): if the
bit at i is 0, the reduced label is not the position of i; if it is 1,
the reduced label is at most that position.

\begin{code}

reduced-avoids : (n : ℕ) (c : Fin n → 𝟚) (i : Fin n) → c i ＝ ₀
               → ¬ (reduced n c ＝ position n i)
reduced-avoids n c i e s = zero-is-not-one (e ⁻¹ ∙ reduced-hit n c i s)

reduced-at-most : (n : ℕ) (c : Fin n → 𝟚) (i : Fin n) → c i ＝ ₁
                → reduced n c ≤ position n i
reduced-at-most n c i e = not-less-bigger-or-equal (reduced n c) (position n i)
                           (λ l →
                             zero-is-not-one (reduced-before n c i l ⁻¹ ∙ e))

\end{code}

Codes, their vertices and labels, doors and completeness.

\begin{code}

Code : ℕ → 𝓤₀ ̇
Code n = (Fin n → ℕ) × (Fin n → ℕ)

Labelling : ℕ → 𝓤₀ ̇
Labelling n = (Fin n → ℕ) → Fin n → 𝟚

lt : ℕ → ℕ → 𝟚
lt x k = χ (<-decidable x k)

vertex-bits : {n : ℕ} → (Fin n → ℕ) → ℕ → Fin n → 𝟚
vertex-bits r k i = lt (r i) k

vertex : {n : ℕ} → Code n → ℕ → Fin n → ℕ
vertex (b , r) k = corner b (vertex-bits r k)

label : (n : ℕ) → Labelling n → Code n → ℕ → ℕ
label n ℓ c k = reduced n (ℓ (vertex c k))

labels : (n : ℕ) → Labelling n → Code n → List ℕ
labels n ℓ c = map (label n ℓ c) (range (succ n))

door : (n : ℕ) → Labelling n → Code n → ℕ → 𝟚
door n ℓ c k =
 χ (⊆-decidable ℕ-is-discrete (range n) (remove-at k (labels n ℓ c)))

complete : (n : ℕ) → Labelling n → Code n → 𝟚
complete n ℓ c = χ (⊆-decidable ℕ-is-discrete (range (succ n)) (labels n ℓ c))

\end{code}

K2: a code has an odd number of doors exactly when it is complete.

\begin{code}

labels-length : (n : ℕ) (ℓ : Labelling n) (c : Code n)
              → length (labels n ℓ c) ＝ succ n
labels-length n ℓ c =
 length-map (label n ℓ c) (range (succ n)) ∙ length-range (succ n)

labels-bound : (n : ℕ) (ℓ : Labelling n) (c : Code n) (y : ℕ) → y ∈ labels n ℓ c
             → y ≤ n
labels-bound n ℓ c y m =
 transport (_≤ n) (pr₂ (pr₂ r)) (reduced-bound n (ℓ (vertex c (pr₁ r))))
 where
  r = ∈-map⁻¹ (label n ℓ c) (range (succ n)) m

doors-of-a-code : (n : ℕ) (ℓ : Labelling n) (c : Code n)
                → sum (door n ℓ c) (range (succ n)) ＝ complete n ℓ c
doors-of-a-code n ℓ c =
 ap (λ - → sum (door n ℓ c) (range -)) (labels-length n ℓ c ⁻¹)
 ∙ door-count ℕ-is-discrete (labels n ℓ c) (range n) (range-dup-free n)
    (labels-length n ℓ c ∙ ap succ (length-range n ⁻¹))
 ∙ χ-↔
 (×-preserves-decidability (⊆-decidable ℕ-is-discrete (range n) (labels n ℓ c))
                           (outside-decidable ℕ-is-discrete (labels n ℓ c)
                             (range n)))
       (⊆-decidable ℕ-is-discrete (range (succ n)) (labels n ℓ c))
       there back
 where
  there : (range n ⊆ labels n ℓ c)
        × outside ℕ-is-discrete (labels n ℓ c) (range n)
        → range (succ n) ⊆ labels n ℓ c
  there (h , y , m , u) z mz = cases (λ l → h z (range-member⁻¹ z n l))
                                     (λ e → transport (_∈ labels n ℓ c)
                                             (y-is-n ∙ e ⁻¹) m)
                                     (<-split z n (range-member z (succ n) mz))
   where
    y-is-n : y ＝ n
    y-is-n = ≤-anti y n (labels-bound n ℓ c y m)
              (not-less-bigger-or-equal n y (λ l → u (range-member⁻¹ y n l)))

  back : range (succ n) ⊆ labels n ℓ c
       → (range n ⊆ labels n ℓ c)
       × outside ℕ-is-discrete (labels n ℓ c) (range n)
  back h = (λ z mz → h z (range-member⁻¹ z (succ n)
                            (<-trans z n (succ n) (range-member z n mz)
                              (<-succ n)))) ,
           (n , h n (range-member⁻¹ n (succ n) (<-succ n)) ,
            (λ mn → not-less-than-itself n (range-member n n mn)))

\end{code}

Arithmetic, finite search, the list of the elements of Fin n, and two
facts about removing an entry from a list of labels.

\begin{code}

succ-pred : (x : ℕ) → ¬ (x ＝ 0) → succ (pred x) ＝ x
succ-pred 0        ne = 𝟘-elim (ne refl)
succ-pred (succ x) ne = refl

pred-≤ : (x : ℕ) → pred x ≤ x
pred-≤ 0        = ⋆
pred-≤ (succ x) = ≤-succ x

pred-< : (x : ℕ) → ¬ (x ＝ 0) → pred x < x
pred-< 0        ne = 𝟘-elim (ne refl)
pred-< (succ x) ne = <-succ x

≤-≠-< : (x y : ℕ) → x ≤ y → ¬ (x ＝ y) → x < y
≤-≠-< 0        0        l ne = 𝟘-elim (ne refl)
≤-≠-< 0        (succ y) l ne = ⋆
≤-≠-< (succ x) 0        l ne = 𝟘-elim l
≤-≠-< (succ x) (succ y) l ne = ≤-≠-< x y l (λ e → ne (ap succ e))

lt-step : (a j : ℕ) → ¬ (j ＝ succ a) → lt a j ＝ lt (succ a) j
lt-step a j ne = χ-↔ (<-decidable a j) (<-decidable (succ a) j)
                  (λ l → ≤-≠-< (succ a) j l (λ e → ne (e ⁻¹)))
                  (λ l → <-trans a (succ a) j (<-succ a) l)

lt-no : (x k : ℕ) → ¬ (x < k) → lt x k ＝ ₀
lt-no x k = χ-no (<-decidable x k)

¬-decidable : {A : 𝓤 ̇ } → is-decidable A → is-decidable (¬ A)
¬-decidable (inl a) = inr (λ u → u a)
¬-decidable (inr u) = inl u

Fin-∀-decidable : (n : ℕ) (P : Fin n → 𝓤 ̇ )
                → ((i : Fin n) → is-decidable (P i))
                → is-decidable ((i : Fin n) → P i)
Fin-∀-decidable 0        P d = inl (λ i → 𝟘-elim i)
Fin-∀-decidable (succ m) P d =
 γ (d (inr ⋆)) (Fin-∀-decidable m (λ i → P (inl i)) (λ i → d (inl i)))
 where
  γ : is-decidable (P (inr ⋆)) → is-decidable ((i : Fin m) → P (inl i))
    → is-decidable ((i : Fin (succ m)) → P i)
  γ (inl a) (inl h) = inl δ
   where
    δ : (i : Fin (succ m)) → P i
    δ (inl i) = h i
    δ (inr ⋆) = a
  γ (inl a) (inr v) = inr (λ h → v (λ i → h (inl i)))
  γ (inr u) _       = inr (λ h → u (h (inr ⋆)))

Fin-∃-decidable : (n : ℕ) (P : Fin n → 𝓤 ̇ )
                → ((i : Fin n) → is-decidable (P i))
                → is-decidable (Σ i ꞉ Fin n , P i)
Fin-∃-decidable 0        P d = inr (λ s → 𝟘-elim (pr₁ s))
Fin-∃-decidable (succ m) P d =
 γ (d (inr ⋆)) (Fin-∃-decidable m (λ i → P (inl i)) (λ i → d (inl i)))
 where
  γ : is-decidable (P (inr ⋆)) → is-decidable (Σ i ꞉ Fin m , P (inl i))
    → is-decidable (Σ i ꞉ Fin (succ m) , P i)
  γ (inl a) _       = inl (inr ⋆ , a)
  γ (inr u) (inl s) = inl (inl (pr₁ s) , pr₂ s)
  γ (inr u) (inr v) = inr δ
   where
    δ : ¬ (Σ i ꞉ Fin (succ m) , P i)
    δ (inl i , q) = v (i , q)
    δ (inr ⋆ , q) = u q

Fin-list : (n : ℕ) → List (Fin n)
Fin-list 0        = []
Fin-list (succ n) = inr ⋆ ∷ map inl (Fin-list n)

Fin-list-dup-free : (n : ℕ) → dup-free (Fin-list n)
Fin-list-dup-free 0        = ⋆
Fin-list-dup-free (succ n) =
 γ , dup-free-map inl (λ i i' → inl-lc) (Fin-list n) (Fin-list-dup-free n)
 where
  γ : ¬ (inr ⋆ ∈ map inl (Fin-list n))
  γ m = +disjoint (pr₂ (pr₂ (∈-map⁻¹ inl (Fin-list n) m)))

Fin-list-length : (n : ℕ) → length (Fin-list n) ＝ n
Fin-list-length 0        = refl
Fin-list-length (succ n) =
 ap succ (length-map inl (Fin-list n) ∙ Fin-list-length n)

map-ext : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y) (xs : List X)
        → ((x : X) → x ∈ xs → f x ＝ g x) → map f xs ＝ map g xs
map-ext f g []       e = refl
map-ext f g (x ∷ xs) e =
 ap₂ _∷_ (e x (inl refl)) (map-ext f g xs (λ y m → e y (inr m)))

remove-last : {X : 𝓤 ̇ } (f : ℕ → X) (n : ℕ)
            → remove-at n (map f (range (succ n))) ＝ map f (range n)
remove-last f 0        = refl
remove-last f (succ n) =
 ap (λ - → f 0 ∷ remove-at n -) (map-∘ succ f (range (succ n)) ⁻¹)
                       ∙ ap (f 0 ∷_) (remove-last (λ j → f (succ j)) n)
                       ∙ ap (f 0 ∷_) (map-∘ succ f (range n))

remove-at-agree : {X : 𝓤 ̇ } (f g : ℕ → X) (k n : ℕ)
                → ((j : ℕ) → ¬ (j ＝ k) → f j ＝ g j)
                → remove-at k (map f (range n)) ＝ remove-at k (map g (range n))
remove-at-agree f g k        0        e = refl
remove-at-agree f g 0        (succ n) e =
 map-∘ succ f (range n) ⁻¹
 ∙ map-ext (λ j → f (succ j)) (λ j → g (succ j)) (range n)
    (λ j _ → e (succ j) (positive-not-zero j))
 ∙ map-∘ succ g (range n)
remove-at-agree f g (succ k) (succ n) e =
 ap₂ _∷_ (e 0 (λ z → positive-not-zero k (z ⁻¹)))
  (ap (remove-at k) (map-∘ succ f (range n) ⁻¹)
   ∙ remove-at-agree (λ j → f (succ j)) (λ j → g (succ j)) k n
      (λ j ne → e (succ j) (λ z → ne (succ-lc z)))
   ∙ ap (remove-at k) (map-∘ succ g (range n)))

\end{code}

Validity, and K3: a rank function that is injective takes every value
below n, by the pigeonhole principle.

\begin{code}

Valid : (n p : ℕ) → Code n → 𝓤₀ ̇
Valid n p (b , r) = ((i : Fin n) → b i ≤ p)
                  × ((i : Fin n) → r i < n)
                  × ((i j : Fin n) → r i ＝ r j → i ＝ j)

Valid-decidable : (n p : ℕ) (c : Code n) → is-decidable (Valid n p c)
Valid-decidable n p (b , r) =
 ×-preserves-decidability
  (Fin-∀-decidable n (λ i → b i ≤ p) (λ i → ≤-decidable (b i) p))
  (×-preserves-decidability
    (Fin-∀-decidable n (λ i → r i < n) (λ i → <-decidable (r i) n))
    (Fin-∀-decidable n (λ i → (j : Fin n) → r i ＝ r j → i ＝ j)
      (λ i → Fin-∀-decidable n (λ j → r i ＝ r j → i ＝ j)
               (λ j → →-preserves-decidability (ℕ-is-discrete (r i) (r j))
                       (Fin-is-discrete i j)))))

valid-ranks-take-every-value : (n p : ℕ) (c : Code n) → Valid n p c
                             → (j : ℕ) → j < n → Σ i ꞉ Fin n , pr₂ c i ＝ j
valid-ranks-take-every-value n p (b , r) (bb , rb , ri) j l =
 γ (Fin-∃-decidable n (λ i → r i ＝ j) (λ i → ℕ-is-discrete (r i) j))
 where
  γ : is-decidable (Σ i ꞉ Fin n , r i ＝ j) → Σ i ꞉ Fin n , r i ＝ j
  γ (inl s) = s
  γ (inr u) = 𝟘-elim (too-short ℕ-is-discrete (map r (Fin-list n))
                       (remove ℕ-is-discrete j (range n))
                       (dup-free-map r ri (Fin-list n) (Fin-list-dup-free n))
                        sub short)
   where
    sub : map r (Fin-list n) ⊆ remove ℕ-is-discrete j (range n)
    sub z mz = remove-member⁻¹ ℕ-is-discrete j z (range n)
                (range-member⁻¹ z n
                  (transport (_< n) (pr₂ (pr₂ t)) (rb (pr₁ t))))
                (λ e → u (pr₁ t , (pr₂ (pr₂ t) ∙ e)))
     where
      t = ∈-map⁻¹ r (Fin-list n) mz

    short : length (remove ℕ-is-discrete j (range n))
          < length (map r (Fin-list n))
    short = transport (length (remove ℕ-is-discrete j (range n)) <_)
             (length-range n
              ∙ (length-map r (Fin-list n) ∙ Fin-list-length n) ⁻¹)
             (remove-length-strict ℕ-is-discrete j (range n)
               (range-member⁻¹ j n l))

\end{code}

K4. The exchange of the ranks k and k + 1, and the moves, in dimension
n = m + 1. A flag is a code with an index. A flag is good if its code
is valid, its index is at most n, and it is not blocked: blocked at
index 0 means base p (= N − 1) at the coordinate of rank 0, and
blocked at index n means base 0 at the coordinate of rank n − 1 = m.

\begin{code}

Flag : ℕ → 𝓤₀ ̇
Flag n = Code n × ℕ

swap : ℕ → ℕ → ℕ
swap k x = ite (ℕ-is-discrete x k) (succ k) (ite (ℕ-is-discrete x (succ k)) k x)

swap-involutive : (k x : ℕ) → swap k (swap k x) ＝ x
swap-involutive k x = γ (ℕ-is-discrete x k) (ℕ-is-discrete x (succ k))
 where
  sk≠k : ¬ (succ k ＝ k)
  sk≠k e = succ-no-fp k (e ⁻¹)

  γ : is-decidable (x ＝ k) → is-decidable (x ＝ succ k) → swap k (swap k x) ＝ x
  γ (inl e) _        = ap (swap k) (ite-yes (ℕ-is-discrete x k) e)
                     ∙ ite-no (ℕ-is-discrete (succ k) k) sk≠k
                     ∙ ite-yes (ℕ-is-discrete (succ k) (succ k)) refl
                     ∙ e ⁻¹
  γ (inr u) (inl e') = ap (swap k)
   (ite-no (ℕ-is-discrete x k) u ∙ ite-yes (ℕ-is-discrete x (succ k)) e')
                     ∙ ite-yes (ℕ-is-discrete k k) refl
                     ∙ e' ⁻¹
  γ (inr u) (inr v)  = ap (swap k) s ∙ s
   where
    s : swap k x ＝ x
    s = ite-no (ℕ-is-discrete x k) u ∙ ite-no (ℕ-is-discrete x (succ k)) v

swap-injective : (k x y : ℕ) → swap k x ＝ swap k y → x ＝ y
swap-injective k x y e =
 swap-involutive k x ⁻¹ ∙ ap (swap k) e ∙ swap-involutive k y

lt-swap : (k j x : ℕ) → ¬ (j ＝ succ k) → lt (swap k x) j ＝ lt x j
lt-swap k j x ne = γ (ℕ-is-discrete x k) (ℕ-is-discrete x (succ k))
 where
  γ : is-decidable (x ＝ k) → is-decidable (x ＝ succ k)
    → lt (swap k x) j ＝ lt x j
  γ (inl e) _        = ap (λ - → lt - j) (ite-yes (ℕ-is-discrete x k) e)
                     ∙ lt-step k j ne ⁻¹
                     ∙ ap (λ - → lt - j) (e ⁻¹)
  γ (inr u) (inl e') = ap (λ - → lt - j)
   (ite-no (ℕ-is-discrete x k) u ∙ ite-yes (ℕ-is-discrete x (succ k)) e')
                     ∙ lt-step k j ne
                     ∙ ap (λ - → lt - j) (e' ⁻¹)
  γ (inr u) (inr v)  = ap (λ - → lt - j)
   (ite-no (ℕ-is-discrete x k) u ∙ ite-no (ℕ-is-discrete x (succ k)) v)

module moves (fe : funext 𝓤₀ 𝓤₀) (m p : ℕ) where

 n : ℕ
 n = succ m

 base-up : (Fin n → ℕ) → (Fin n → ℕ) → Fin n → ℕ
 base-up b r i = ite (ℕ-is-discrete (r i) 0) (succ (b i)) (b i)

 rank-down : ℕ → ℕ
 rank-down x = ite (ℕ-is-discrete x 0) m (pred x)

 base-down : (Fin n → ℕ) → (Fin n → ℕ) → Fin n → ℕ
 base-down b r i = ite (ℕ-is-discrete (r i) m) (pred (b i)) (b i)

 rank-up : ℕ → ℕ
 rank-up x = ite (ℕ-is-discrete x m) 0 (succ x)

 move-succ : (b r : Fin n → ℕ) (k : ℕ) → is-decidable (k ＝ m) → Flag n
 move-succ b r k (inl _) = (base-down b r , (λ i → rank-up (r i))) , 0
 move-succ b r k (inr _) = (b , (λ i → swap k (r i))) , succ k

 move : Flag n → Flag n
 move ((b , r) , 0)      = (base-up b r , (λ i → rank-down (r i))) , n
 move ((b , r) , succ k) = move-succ b r k (ℕ-is-discrete k m)

 Blocked : Flag n → 𝓤₀ ̇
 Blocked ((b , r) , 0)      = Σ i ꞉ Fin n , (r i ＝ 0) × (b i ＝ p)
 Blocked ((b , r) , succ k) = (k ＝ m) × (Σ i ꞉ Fin n , (r i ＝ m) × (b i ＝ 0))

 Blocked-decidable : (x : Flag n) → is-decidable (Blocked x)
 Blocked-decidable ((b , r) , 0) =
  Fin-∃-decidable n (λ i → (r i ＝ 0) × (b i ＝ p))
   (λ i →
     ×-preserves-decidability (ℕ-is-discrete (r i) 0) (ℕ-is-discrete (b i) p))
 Blocked-decidable ((b , r) , succ k) =
  ×-preserves-decidability (ℕ-is-discrete k m)
   (Fin-∃-decidable n (λ i → (r i ＝ m) × (b i ＝ 0))
     (λ i → ×-preserves-decidability (ℕ-is-discrete (r i) m)
             (ℕ-is-discrete (b i) 0)))

 Good : Flag n → 𝓤₀ ̇
 Good (c , k) = Valid n p c × (k ≤ n) × ¬ Blocked (c , k)

 Good-decidable : (x : Flag n) → is-decidable (Good x)
 Good-decidable (c , k) =
  ×-preserves-decidability (Valid-decidable n p c)
   (×-preserves-decidability (≤-decidable k n)
     (¬-decidable (Blocked-decidable (c , k))))

 Door : Labelling n → Flag n → 𝟚
 Door ℓ (c , k) = door n ℓ c k

\end{code}

The move at index 0: add 1 to the base at the coordinate of rank 0,
give it rank m, lower the other ranks by 1; the new index is n. Vertex
j of the new code is vertex j + 1 of the old one, for j < n.

\begin{code}

 module at-zero (b r : Fin n → ℕ) (v : Valid n p (b , r))
                (nb : ¬ Blocked ((b , r) , 0)) where

  b⁺ : Fin n → ℕ
  b⁺ = base-up b r

  r⁻ : Fin n → ℕ
  r⁻ i = rank-down (r i)

  up : Flag n
  up = (b⁺ , r⁻) , n

  b⁺-at-0 : (i : Fin n) → r i ＝ 0 → b⁺ i ＝ succ (b i)
  b⁺-at-0 i z = ite-yes (ℕ-is-discrete (r i) 0) z

  b⁺-off-0 : (i : Fin n) → ¬ (r i ＝ 0) → b⁺ i ＝ b i
  b⁺-off-0 i nz = ite-no (ℕ-is-discrete (r i) 0) nz

  r⁻-at-0 : (i : Fin n) → r i ＝ 0 → r⁻ i ＝ m
  r⁻-at-0 i z = ite-yes (ℕ-is-discrete (r i) 0) z

  r⁻-off-0 : (i : Fin n) → ¬ (r i ＝ 0) → r⁻ i ＝ pred (r i)
  r⁻-off-0 i nz = ite-no (ℕ-is-discrete (r i) 0) nz

  r⁻-is-m : (i : Fin n) → r⁻ i ＝ m → r i ＝ 0
  r⁻-is-m i e = γ (ℕ-is-discrete (r i) 0)
   where
    γ : is-decidable (r i ＝ 0) → r i ＝ 0
    γ (inl z)  = z
    γ (inr nz) = 𝟘-elim (not-less-than-itself n
                  (transport (_< n)
                    (succ-pred (r i) nz ⁻¹ ∙ ap succ (r⁻-off-0 i nz ⁻¹ ∙ e))
                    (pr₁ (pr₂ v) i)))

  valid-up : Valid n p (b⁺ , r⁻)
  valid-up = bounds , ranks , injective
   where
    bounds : (i : Fin n) → b⁺ i ≤ p
    bounds i = γ (ℕ-is-discrete (r i) 0)
     where
      γ : is-decidable (r i ＝ 0) → b⁺ i ≤ p
      γ (inl z)  = transport (_≤ p) (b⁺-at-0 i z ⁻¹)
                    (≤-≠-< (b i) p (pr₁ v i) (λ e → nb (i , z , e)))
      γ (inr nz) = transport (_≤ p) (b⁺-off-0 i nz ⁻¹) (pr₁ v i)

    ranks : (i : Fin n) → r⁻ i < n
    ranks i = γ (ℕ-is-discrete (r i) 0)
     where
      γ : is-decidable (r i ＝ 0) → r⁻ i < n
      γ (inl z)  = transport (_< n) (r⁻-at-0 i z ⁻¹) (<-succ m)
      γ (inr nz) = transport (_< n) (r⁻-off-0 i nz ⁻¹)
                    (≤-<-trans (pred (r i)) (r i) n (pred-≤ (r i))
                      (pr₁ (pr₂ v) i))

    injective : (i j : Fin n) → r⁻ i ＝ r⁻ j → i ＝ j
    injective i j e = γ (ℕ-is-discrete (r i) 0) (ℕ-is-discrete (r j) 0)
     where
      γ : is-decidable (r i ＝ 0) → is-decidable (r j ＝ 0) → i ＝ j
      γ (inl zi) (inl zj) = pr₂ (pr₂ v) i j (zi ∙ zj ⁻¹)
      γ (inl zi) (inr nj) = 𝟘-elim (nj (r⁻-is-m j (e ⁻¹ ∙ r⁻-at-0 i zi)))
      γ (inr ni) (inl zj) = 𝟘-elim (ni (r⁻-is-m i (e ∙ r⁻-at-0 j zj)))
      γ (inr ni) (inr nj) = pr₂ (pr₂ v) i j
                             (succ-pred (r i) ni ⁻¹
                              ∙ ap succ (r⁻-off-0 i ni ⁻¹ ∙ e ∙ r⁻-off-0 j nj)
                              ∙ succ-pred (r j) nj)

  movable-up : (n ≤ n) × ¬ Blocked up
  movable-up = ≤-refl n , γ
   where
    γ : ¬ Blocked up
    γ (_ , i , e₁ , e₂) =
     positive-not-zero (b i) (b⁺-at-0 i (r⁻-is-m i e₁) ⁻¹ ∙ e₂)

  move-move-at-zero : move up ＝ ((b , r) , 0)
  move-move-at-zero = γ (ℕ-is-discrete m m)
   where
    base-back : base-down b⁺ r⁻ ∼ b
    base-back i = δ (ℕ-is-discrete (r i) 0)
     where
      δ : is-decidable (r i ＝ 0) → base-down b⁺ r⁻ i ＝ b i
      δ (inl z)  =
       ite-yes (ℕ-is-discrete (r⁻ i) m) (r⁻-at-0 i z) ∙ ap pred (b⁺-at-0 i z)
      δ (inr nz) =
       ite-no (ℕ-is-discrete (r⁻ i) m) (λ e → nz (r⁻-is-m i e)) ∙ b⁺-off-0 i nz

    rank-back : (λ i → rank-up (r⁻ i)) ∼ r
    rank-back i = δ (ℕ-is-discrete (r i) 0)
     where
      δ : is-decidable (r i ＝ 0) → rank-up (r⁻ i) ＝ r i
      δ (inl z)  = ite-yes (ℕ-is-discrete (r⁻ i) m) (r⁻-at-0 i z) ∙ z ⁻¹
      δ (inr nz) = ite-no (ℕ-is-discrete (r⁻ i) m) (λ e → nz (r⁻-is-m i e))
                 ∙ ap succ (r⁻-off-0 i nz) ∙ succ-pred (r i) nz

    γ : (d : is-decidable (m ＝ m)) → move-succ b⁺ r⁻ m d ＝ ((b , r) , 0)
    γ (inl _) =
     ap (_, 0) (ap₂ _,_ (dfunext fe base-back) (dfunext fe rank-back))
    γ (inr u) = 𝟘-elim (u refl)

  up-is-different : ¬ (up ＝ ((b , r) , 0))
  up-is-different e = positive-not-zero m (ap pr₂ e)

  vertex-up : (j : ℕ) → j < n → vertex (b⁺ , r⁻) j ＝ vertex (b , r) (succ j)
  vertex-up j l = dfunext fe γ
   where
    γ : (i : Fin n) → vertex (b⁺ , r⁻) j i ＝ vertex (b , r) (succ j) i
    γ i = δ (ℕ-is-discrete (r i) 0)
     where
      δ : is-decidable (r i ＝ 0)
        → b⁺ i +ℕ bit (lt (r⁻ i) j) ＝ b i +ℕ bit (lt (r i) (succ j))
      δ (inl z)  = ap₂ (λ x y → x +ℕ bit y) (b⁺-at-0 i z)
                    (ap (λ - → lt - j) (r⁻-at-0 i z)
                     ∙ lt-no m j
                        (λ l' → not-less-than-itself m (<-≤-trans m j m l' l)))
                 ∙ ap (λ - → b i +ℕ bit (lt - (succ j))) (z ⁻¹)
      δ (inr nz) = ap₂ (λ x y → x +ℕ bit y) (b⁺-off-0 i nz)
                    (ap (λ - → lt - j) (r⁻-off-0 i nz))
                 ∙ ap (λ - → b i +ℕ bit (lt - (succ j))) (succ-pred (r i) nz)

  door-up : (ℓ : Labelling n) → door n ℓ (b⁺ , r⁻) n ＝ door n ℓ (b , r) 0
  door-up ℓ = ap (λ L → χ (⊆-decidable ℕ-is-discrete (range n) L)) lists
   where
    lists : remove-at n (labels n ℓ (b⁺ , r⁻))
          ＝ remove-at 0 (labels n ℓ (b , r))
    lists = remove-last (label n ℓ (b⁺ , r⁻)) n
          ∙ map-ext (label n ℓ (b⁺ , r⁻)) (λ j → label n ℓ (b , r) (succ j))
             (range n)
              (λ j mj →
                ap (λ w → reduced n (ℓ w)) (vertex-up j (range-member j n mj)))
          ∙ map-∘ succ (label n ℓ (b , r)) (range n)

\end{code}

The move at index n, the inverse of the last one: subtract 1 from the
base at the coordinate of rank m, give it rank 0, raise the other
ranks by 1; the new index is 0.

\begin{code}

 module at-top (b r : Fin n → ℕ) (v : Valid n p (b , r))
               (nb : ¬ Blocked ((b , r) , n)) where

  b⁻ : Fin n → ℕ
  b⁻ = base-down b r

  r⁺ : Fin n → ℕ
  r⁺ i = rank-up (r i)

  down : Flag n
  down = (b⁻ , r⁺) , 0

  move-at-top : move ((b , r) , n) ＝ down
  move-at-top = γ (ℕ-is-discrete m m)
   where
    γ : (d : is-decidable (m ＝ m)) → move-succ b r m d ＝ down
    γ (inl _) = refl
    γ (inr u) = 𝟘-elim (u refl)

  r⁺-at-m : (i : Fin n) → r i ＝ m → r⁺ i ＝ 0
  r⁺-at-m i e = ite-yes (ℕ-is-discrete (r i) m) e

  r⁺-off-m : (i : Fin n) → ¬ (r i ＝ m) → r⁺ i ＝ succ (r i)
  r⁺-off-m i ne = ite-no (ℕ-is-discrete (r i) m) ne

  b⁻-at-m : (i : Fin n) → r i ＝ m → b⁻ i ＝ pred (b i)
  b⁻-at-m i e = ite-yes (ℕ-is-discrete (r i) m) e

  b⁻-off-m : (i : Fin n) → ¬ (r i ＝ m) → b⁻ i ＝ b i
  b⁻-off-m i ne = ite-no (ℕ-is-discrete (r i) m) ne

  r⁺-is-0 : (i : Fin n) → r⁺ i ＝ 0 → r i ＝ m
  r⁺-is-0 i e = γ (ℕ-is-discrete (r i) m)
   where
    γ : is-decidable (r i ＝ m) → r i ＝ m
    γ (inl e') = e'
    γ (inr ne) = 𝟘-elim (positive-not-zero (r i) (r⁺-off-m i ne ⁻¹ ∙ e))

  base-positive : (i : Fin n) → r i ＝ m → ¬ (b i ＝ 0)
  base-positive i e z = nb (refl , i , e , z)

  valid-down : Valid n p (b⁻ , r⁺)
  valid-down = bounds , ranks , injective
   where
    bounds : (i : Fin n) → b⁻ i ≤ p
    bounds i = γ (ℕ-is-discrete (r i) m)
     where
      γ : is-decidable (r i ＝ m) → b⁻ i ≤ p
      γ (inl e)  = transport (_≤ p) (b⁻-at-m i e ⁻¹)
                    (≤-trans (pred (b i)) (b i) p (pred-≤ (b i)) (pr₁ v i))
      γ (inr ne) = transport (_≤ p) (b⁻-off-m i ne ⁻¹) (pr₁ v i)

    ranks : (i : Fin n) → r⁺ i < n
    ranks i = γ (ℕ-is-discrete (r i) m)
     where
      γ : is-decidable (r i ＝ m) → r⁺ i < n
      γ (inl e)  = transport (_< n) (r⁺-at-m i e ⁻¹) ⋆
      γ (inr ne) = transport (_< n) (r⁺-off-m i ne ⁻¹)
                    (cases id (λ e → 𝟘-elim (ne e))
                      (<-split (r i) m (pr₁ (pr₂ v) i)))

    injective : (i j : Fin n) → r⁺ i ＝ r⁺ j → i ＝ j
    injective i j e = γ (ℕ-is-discrete (r i) m) (ℕ-is-discrete (r j) m)
     where
      γ : is-decidable (r i ＝ m) → is-decidable (r j ＝ m) → i ＝ j
      γ (inl ei) (inl ej) = pr₂ (pr₂ v) i j (ei ∙ ej ⁻¹)
      γ (inl ei) (inr nj) = 𝟘-elim (nj (r⁺-is-0 j (e ⁻¹ ∙ r⁺-at-m i ei)))
      γ (inr ni) (inl ej) = 𝟘-elim (ni (r⁺-is-0 i (e ∙ r⁺-at-m j ej)))
      γ (inr ni) (inr nj) =
       pr₂ (pr₂ v) i j (succ-lc (r⁺-off-m i ni ⁻¹ ∙ e ∙ r⁺-off-m j nj))

  movable-down : (0 ≤ n) × ¬ Blocked down
  movable-down = ⋆ , γ
   where
    γ : ¬ Blocked down
    γ (i , e₁ , e₂) = not-less-than-itself p
                       (transport (_< p) (b⁻-at-m i (r⁺-is-0 i e₁) ⁻¹ ∙ e₂)
                         (<-≤-trans (pred (b i)) (b i) p
                           (pred-< (b i) (base-positive i (r⁺-is-0 i e₁)))
                            (pr₁ v i)))

  move-move-at-top : move down ＝ ((b , r) , n)
  move-move-at-top =
   ap (_, n) (ap₂ _,_ (dfunext fe base-back) (dfunext fe rank-back))
   where
    base-back : base-up b⁻ r⁺ ∼ b
    base-back i = γ (ℕ-is-discrete (r i) m)
     where
      γ : is-decidable (r i ＝ m) → base-up b⁻ r⁺ i ＝ b i
      γ (inl e)  =
       ite-yes (ℕ-is-discrete (r⁺ i) 0) (r⁺-at-m i e) ∙ ap succ (b⁻-at-m i e)
                 ∙ succ-pred (b i) (base-positive i e)
      γ (inr ne) =
       ite-no (ℕ-is-discrete (r⁺ i) 0) (λ z → ne (r⁺-is-0 i z)) ∙ b⁻-off-m i ne

    rank-back : (λ i → rank-down (r⁺ i)) ∼ r
    rank-back i = γ (ℕ-is-discrete (r i) m)
     where
      γ : is-decidable (r i ＝ m) → rank-down (r⁺ i) ＝ r i
      γ (inl e)  = ite-yes (ℕ-is-discrete (r⁺ i) 0) (r⁺-at-m i e) ∙ e ⁻¹
      γ (inr ne) = ite-no (ℕ-is-discrete (r⁺ i) 0) (λ z → ne (r⁺-is-0 i z))
                   ∙ ap pred (r⁺-off-m i ne)

  down-is-different : ¬ (down ＝ ((b , r) , n))
  down-is-different e = positive-not-zero m (ap pr₂ e ⁻¹)

\end{code}

The move at an index 0 < k + 1 < n: exchange the ranks k and k + 1.
Only vertex k + 1 changes.

\begin{code}

 module interior (b r : Fin n → ℕ) (v : Valid n p (b , r)) (k : ℕ)
                 (ne : ¬ (k ＝ m))
                 (l : succ k ≤ n) where

  r' : Fin n → ℕ
  r' i = swap k (r i)

  swapped : Flag n
  swapped = (b , r') , succ k

  move-interior : move ((b , r) , succ k) ＝ swapped
  move-interior = γ (ℕ-is-discrete k m)
   where
    γ : (d : is-decidable (k ＝ m)) → move-succ b r k d ＝ swapped
    γ (inl e) = 𝟘-elim (ne e)
    γ (inr _) = refl

  k<m : k < m
  k<m = ≤-≠-< k m l ne

  valid-swapped : Valid n p (b , r')
  valid-swapped =
   pr₁ v , ranks , (λ i j e → pr₂ (pr₂ v) i j (swap-injective k (r i) (r j) e))
   where
    ranks : (i : Fin n) → r' i < n
    ranks i = γ (ℕ-is-discrete (r i) k) (ℕ-is-discrete (r i) (succ k))
     where
      γ : is-decidable (r i ＝ k) → is-decidable (r i ＝ succ k) → r' i < n
      γ (inl e) _        =
       transport (_< n) (ite-yes (ℕ-is-discrete (r i) k) e ⁻¹) k<m
      γ (inr u) (inl e') = transport (_< n)
                            ((ite-no (ℕ-is-discrete (r i) k) u
                              ∙ ite-yes (ℕ-is-discrete (r i) (succ k)) e') ⁻¹)
                            (<-trans k m n k<m (<-succ m))
      γ (inr u) (inr u') = transport (_< n)
                            ((ite-no (ℕ-is-discrete (r i) k) u
                              ∙ ite-no (ℕ-is-discrete (r i) (succ k)) u') ⁻¹)
                            (pr₁ (pr₂ v) i)

  movable-swapped : (succ k ≤ n) × ¬ Blocked swapped
  movable-swapped = l , (λ bl → ne (pr₁ bl))

  move-move-interior : move swapped ＝ ((b , r) , succ k)
  move-move-interior = γ (ℕ-is-discrete k m)
   where
    γ : (d : is-decidable (k ＝ m)) → move-succ b r' k d ＝ ((b , r) , succ k)
    γ (inl e) = 𝟘-elim (ne e)
    γ (inr _) =
     ap (λ - → (b , -) , succ k) (dfunext fe (λ i → swap-involutive k (r i)))

  swapped-is-different : ¬ (swapped ＝ ((b , r) , succ k))
  swapped-is-different e =
   succ-no-fp k (pr₂ t ⁻¹ ∙ ap (λ c → pr₂ (pr₁ c) i) e ⁻¹
                  ∙ ite-yes (ℕ-is-discrete (r i) k) (pr₂ t))
   where
    t : Σ i ꞉ Fin n , r i ＝ k
    t =
     valid-ranks-take-every-value n p (b , r) v k (<-trans k m n k<m (<-succ m))

    i : Fin n
    i = pr₁ t

  vertex-swapped : (j : ℕ) → ¬ (j ＝ succ k)
                 → vertex (b , r') j ＝ vertex (b , r) j
  vertex-swapped j nj =
   dfunext fe (λ i → ap (λ - → b i +ℕ bit -) (lt-swap k j (r i) nj))

  door-swapped : (ℓ : Labelling n)
               → door n ℓ (b , r') (succ k) ＝ door n ℓ (b , r) (succ k)
  door-swapped ℓ = ap (λ L → χ (⊆-decidable ℕ-is-discrete (range n) L))
                    (remove-at-agree (label n ℓ (b , r')) (label n ℓ (b , r))
                      (succ k) (succ n)
                      (λ j nj →
                        ap (λ w → reduced n (ℓ w)) (vertex-swapped j nj)))

\end{code}

The door at index n is kept, because the move there is undone by the
move at index 0 of the new flag, which keeps the door.

\begin{code}

 door-at-top : (ℓ : Labelling n) (b r : Fin n → ℕ) (v : Valid n p (b , r))
               (nb : ¬ Blocked ((b , r) , n))
             → door n ℓ (at-top.b⁻ b r v nb , at-top.r⁺ b r v nb) 0
             ＝ door n ℓ (b , r) n
 door-at-top ℓ b r v nb =
  at-zero.door-up (at-top.b⁻ b r v nb) (at-top.r⁺ b r v nb)
   (at-top.valid-down b r v nb)
   (pr₂ (at-top.movable-down b r v nb)) ℓ ⁻¹
  ∙ ap (λ c → door n ℓ c n) (ap pr₁ (at-top.move-move-at-top b r v nb))

\end{code}

K4, as one statement for good flags: the move of a good flag is good
and different, the move at the new flag gives the old flag back, and
the door is kept.

\begin{code}

 good-succ : (b r : Fin n → ℕ) (k : ℕ) → is-decidable (k ＝ m)
           → Good ((b , r) , succ k) → Good (move ((b , r) , succ k))
 good-succ b r k (inl refl) (v , _ , nb) =
  transport Good (at-top.move-at-top b r v nb ⁻¹)
   (at-top.valid-down b r v nb , at-top.movable-down b r v nb)
 good-succ b r k (inr ne) (v , l , _) =
  transport Good (interior.move-interior b r v k ne l ⁻¹)
   (interior.valid-swapped b r v k ne l , interior.movable-swapped b r v k ne l)

 move-is-good : (x : Flag n) → Good x → Good (move x)
 move-is-good ((b , r) , 0)      (v , _ , nb) =
  at-zero.valid-up b r v nb , at-zero.movable-up b r v nb
 move-is-good ((b , r) , succ k) g            =
  good-succ b r k (ℕ-is-discrete k m) g

 move-move-succ : (b r : Fin n → ℕ) (k : ℕ) → is-decidable (k ＝ m)
                → Good ((b , r) , succ k)
                → move (move ((b , r) , succ k)) ＝ ((b , r) , succ k)
 move-move-succ b r k (inl refl) (v , _ , nb) =
  ap move (at-top.move-at-top b r v nb) ∙ at-top.move-move-at-top b r v nb
 move-move-succ b r k (inr ne) (v , l , _) =
  ap move (interior.move-interior b r v k ne l)
   ∙ interior.move-move-interior b r v k ne l

 move-move : (x : Flag n) → Good x → move (move x) ＝ x
 move-move ((b , r) , 0)      (v , _ , nb) = at-zero.move-move-at-zero b r v nb
 move-move ((b , r) , succ k) g            =
  move-move-succ b r k (ℕ-is-discrete k m) g

 move-changes-succ : (b r : Fin n → ℕ) (k : ℕ) → is-decidable (k ＝ m)
                   → Good ((b , r) , succ k)
                   → ¬ (move ((b , r) , succ k) ＝ ((b , r) , succ k))
 move-changes-succ b r k (inl refl) (v , _ , nb) e =
  at-top.down-is-different b r v nb (at-top.move-at-top b r v nb ⁻¹ ∙ e)
 move-changes-succ b r k (inr ne) (v , l , _) e =
  interior.swapped-is-different b r v k ne l
   (interior.move-interior b r v k ne l ⁻¹ ∙ e)

 move-changes : (x : Flag n) → Good x → ¬ (move x ＝ x)
 move-changes ((b , r) , 0)      (v , _ , nb) = at-zero.up-is-different b r v nb
 move-changes ((b , r) , succ k) g            =
  move-changes-succ b r k (ℕ-is-discrete k m) g

 move-keeps-door-succ : (ℓ : Labelling n) (b r : Fin n → ℕ) (k : ℕ)
                      → is-decidable (k ＝ m)
                      → Good ((b , r) , succ k) → Door ℓ
                         (move ((b , r) , succ k)) ＝ Door ℓ ((b , r) , succ k)
 move-keeps-door-succ ℓ b r k (inl refl) (v , _ , nb) =
  ap (Door ℓ) (at-top.move-at-top b r v nb) ∙ door-at-top ℓ b r v nb
 move-keeps-door-succ ℓ b r k (inr ne) (v , l , _) =
  ap (Door ℓ) (interior.move-interior b r v k ne l)
   ∙ interior.door-swapped b r v k ne l ℓ

 move-keeps-door : (ℓ : Labelling n) (x : Flag n) → Good x
                 → Door ℓ (move x) ＝ Door ℓ x
 move-keeps-door ℓ ((b , r) , 0)      (v , _ , nb) = at-zero.door-up b r v nb ℓ
 move-keeps-door ℓ ((b , r) , succ k) g            =
  move-keeps-door-succ ℓ b r k (ℕ-is-discrete k m) g

\end{code}

The lists of bases, ranks, codes and flags over which the sums run,
and the sum that K5 and K6 compute: the number of valid complete
codes, modulo 2.

\begin{code}

_&_ : 𝟚 → 𝟚 → 𝟚
₀ & b = ₀
₁ & b = b

&-sum : {X : 𝓤 ̇ } (a : 𝟚) (f : X → 𝟚) (xs : List X)
      → sum (λ x → a & f x) xs ＝ a & sum f xs
&-sum ₀ f xs = sum-of-zeros (λ x → ₀) xs (λ x _ → refl)
&-sum ₁ f xs = refl

&-one-left : (a b : 𝟚) → a & b ＝ ₁ → a ＝ ₁
&-one-left ₀ b e = e
&-one-left ₁ b e = refl

&-one-right : (a b : 𝟚) → a & b ＝ ₁ → b ＝ ₁
&-one-right ₀ b e = 𝟘-elim (zero-is-not-one e)
&-one-right ₁ b e = e

bases : (n p : ℕ) → List (Fin n → ℕ)
bases n p = functions n (range (succ p))

ranks : (n : ℕ) → List (Fin n → ℕ)
ranks n = functions n (range n)

codes : (n p : ℕ) → List (Code n)
codes n p = product (bases n p) (ranks n)

flags : (n p : ℕ) → List (Flag n)
flags n p = product (codes n p) (range (succ n))

parity : (n p : ℕ) → Labelling n → 𝟚
parity n p ℓ =
 sum (λ c → χ (Valid-decidable n p c) & complete n ℓ c) (codes n p)

Lower Upper : (n p : ℕ) → Labelling n → 𝓤₀ ̇
Lower n p ℓ = (a : Fin n → ℕ) → ((j : Fin n) → a j ≤ succ p) → (i : Fin n)
              → a i ＝ 0 → ℓ a i ＝ ₀
Upper n p ℓ = (a : Fin n → ℕ) → ((j : Fin n) → a j ≤ succ p) → (i : Fin n)
              → a i ＝ succ p → ℓ a i ＝ ₁

restrict : (m p : ℕ) → Labelling (succ m) → Labelling m
restrict m p ℓ a i = ℓ (cons (succ p) a) (inl i)

bit-bound : (p x : ℕ) (c : 𝟚) → x ≤ p → x +ℕ bit c ≤ succ p
bit-bound p x ₀ l = ≤-trans x p (succ p) l (≤-succ p)
bit-bound p x ₁ l = l

vertex-in-grid : (n p : ℕ) (b r : Fin n → ℕ) → ((i : Fin n) → b i ≤ p)
               → (k : ℕ) (t : Fin n) → vertex (b , r) k t ≤ succ p
vertex-in-grid n p b r h k t = bit-bound p (b t) (lt (r t) k) (h t)

in-flags : funext 𝓤₀ 𝓤₀ → (n p : ℕ) (x : Flag n) → Valid n p (pr₁ x) → pr₂ x ≤ n
         → x ∈ flags n p
in-flags fe n p ((b , r) , k) v l =
 product-member (codes n p) (range (succ n))
  (product-member (bases n p) (ranks n)
    (functions-complete fe n (range (succ p)) b
      (λ i → range-member⁻¹ (b i) (succ p) (pr₁ v i)))
    (functions-complete fe n (range n) r
      (λ i → range-member⁻¹ (r i) n (pr₁ (pr₂ v) i))))
  (range-member⁻¹ k (succ n) l)

flags-index : (n p : ℕ) (x : Flag n) → x ∈ flags n p → pr₂ x ≤ n
flags-index n p x mx = range-member (pr₂ x) (succ n)
 (pr₂ (product-member⁻¹ (codes n p) (range (succ n)) x mx))

flags-dup-free : (n p : ℕ) → dup-free (flags n p)
flags-dup-free n p =
 product-dup-free (codes n p) (range (succ n))
  (product-dup-free (bases n p) (ranks n)
    (functions-dup-free n (range (succ p)) (range-dup-free (succ p)))
    (functions-dup-free n (range n) (range-dup-free n)))
  (range-dup-free (succ n))

flags-are-discrete : funext 𝓤₀ 𝓤₀ → (n : ℕ) → is-discrete (Flag n)
flags-are-discrete fe n = pairs-are-discrete
 (pairs-are-discrete (Fin-functions-are-discrete fe ℕ-is-discrete n)
                     (Fin-functions-are-discrete fe ℕ-is-discrete n))
                                             ℕ-is-discrete

\end{code}

K5, K6 and the step of the induction, in dimension n = m + 1, for a
labelling ℓ with the two boundary conditions.

\begin{code}

module step (fe : funext 𝓤₀ 𝓤₀) (m p : ℕ) (ℓ : Labelling (succ m))
            (lo : Lower (succ m) p ℓ) (hi : Upper (succ m) p ℓ) where

 open moves fe m p

 ℓ̃ : Labelling m
 ℓ̃ = restrict m p ℓ

 V : Code n → 𝟚
 V c = χ (Valid-decidable n p c)

 D : Flag n → 𝟚
 D = Door ℓ

\end{code}

The involution T of K5: the move on good flags, the identity on the
others; the weight is [good] · door.

\begin{code}

 T-step : (x : Flag n) → is-decidable (Good x) → Flag n
 T-step x (inl _) = move x
 T-step x (inr _) = x

 T : Flag n → Flag n
 T x = T-step x (Good-decidable x)

 T-good : (x : Flag n) → Good x → T x ＝ move x
 T-good x g = γ (Good-decidable x)
  where
   γ : (d : is-decidable (Good x)) → T-step x d ＝ move x
   γ (inl _) = refl
   γ (inr u) = 𝟘-elim (u g)

 T-bad : (x : Flag n) → ¬ Good x → T x ＝ x
 T-bad x u = γ (Good-decidable x)
  where
   γ : (d : is-decidable (Good x)) → T-step x d ＝ x
   γ (inl g) = 𝟘-elim (u g)
   γ (inr _) = refl

 W-good : Flag n → 𝟚
 W-good x = χ (Good-decidable x) & D x

 cancel : sum W-good (flags n p) ＝ ₀
 cancel = cancellation (flags-are-discrete fe n) T W-good (flags n p)
           (flags-dup-free n p)
           T-closed T-involutive T-invariant T-free
  where
   T-closed : (x : Flag n) → x ∈ flags n p → T x ∈ flags n p
   T-closed x mx = γ (Good-decidable x)
    where
     γ : (d : is-decidable (Good x)) → T-step x d ∈ flags n p
     γ (inl g) = in-flags fe n p (move x) (pr₁ (move-is-good x g))
                  (pr₁ (pr₂ (move-is-good x g)))
     γ (inr _) = mx

   T-involutive : (x : Flag n) → x ∈ flags n p → T (T x) ＝ x
   T-involutive x mx = γ (Good-decidable x)
    where
     γ : (d : is-decidable (Good x)) → T (T-step x d) ＝ x
     γ (inl g) = T-good (move x) (move-is-good x g) ∙ move-move x g
     γ (inr u) = T-bad x u

   T-invariant : (x : Flag n) → x ∈ flags n p → W-good (T x) ＝ W-good x
   T-invariant x mx = γ (Good-decidable x)
    where
     γ : (d : is-decidable (Good x)) → W-good (T-step x d) ＝ W-good x
     γ (inl g) = ap₂ _&_ (χ-yes (Good-decidable (move x)) (move-is-good x g))
                  (move-keeps-door ℓ x g)
               ∙ ap (_& D x) (χ-yes (Good-decidable x) g) ⁻¹
     γ (inr u) = refl

   T-free : (x : Flag n) → x ∈ flags n p → W-good x ＝ ₁ → ¬ (T x ＝ x)
   T-free x mx e fixed = move-changes x g (T-good x g ⁻¹ ∙ fixed)
    where
     g : Good x
     g = χ-one (Good-decidable x) (&-one-left (χ (Good-decidable x)) (D x) e)

\end{code}

The flags that are valid but not good are blocked. K6: a blocked flag
whose facet is not on the face where the coordinate 𝟎 (examined last)
is N has no door.

\begin{code}

 Boundary : Flag n → 𝓤₀ ̇
 Boundary ((b , r) , k) = (k ＝ 0) × (b (inr ⋆) ＝ p) × (r (inr ⋆) ＝ 0)

 Boundary-decidable : (x : Flag n) → is-decidable (Boundary x)
 Boundary-decidable ((b , r) , k) =
  ×-preserves-decidability (ℕ-is-discrete k 0)
   (×-preserves-decidability (ℕ-is-discrete (b (inr ⋆)) p)
     (ℕ-is-discrete (r (inr ⋆)) 0))

 boundary-is-blocked : (x : Flag n) → Boundary x → Blocked x
 boundary-is-blocked ((b , r) , 0)      (_ , bp , r0) = inr ⋆ , r0 , bp
 boundary-is-blocked ((b , r) , succ k) (e , _)       =
  𝟘-elim (positive-not-zero k e)

 dVB : (x : Flag n) → is-decidable (Valid n p (pr₁ x) × Blocked x)
 dVB x =
  ×-preserves-decidability (Valid-decidable n p (pr₁ x)) (Blocked-decidable x)

 dVBd : (x : Flag n) → is-decidable (Valid n p (pr₁ x) × Boundary x)
 dVBd x =
  ×-preserves-decidability (Valid-decidable n p (pr₁ x)) (Boundary-decidable x)

 W-blocked W-boundary : Flag n → 𝟚
 W-blocked  x = χ (dVB x) & D x
 W-boundary x = χ (dVBd x) & D x

 good-split : (x : Flag n) → pr₂ x ≤ n
            → V (pr₁ x) & D x ＝ W-good x ⊕ W-blocked x
 good-split x l = γ (Valid-decidable n p (pr₁ x)) (Blocked-decidable x)
  where
   R : 𝟚 → 𝟚 → 𝟚
   R a c = (a & D x) ⊕ (c & D x)

   γ : (dv : is-decidable (Valid n p (pr₁ x))) → is-decidable (Blocked x)
     → χ dv & D x ＝ R (χ (Good-decidable x)) (χ (dVB x))
   γ (inl v) (inl bl) = ap₂ R (χ-no (Good-decidable x) (λ g → pr₂ (pr₂ g) bl))
                         (χ-yes (dVB x) (v , bl)) ⁻¹
   γ (inl v) (inr nb) = (ap₂ R (χ-yes (Good-decidable x) (v , l , nb))
                          (χ-no (dVB x) (λ vb → nb (pr₂ vb)))
                         ∙ xor-right-unit (D x)) ⁻¹
   γ (inr nv) _       = ap₂ R (χ-no (Good-decidable x) (λ g → nv (pr₁ g)))
                         (χ-no (dVB x) (λ vb → nv (pr₁ vb))) ⁻¹

 blocked-at-zero : (b r : Fin n → ℕ) → Valid n p (b , r) → (i : Fin m)
                 → r (inl i) ＝ 0 → b (inl i) ＝ p → door n ℓ (b , r) 0 ＝ ₀
 blocked-at-zero b r v i ri bi =
  χ-no (⊆-decidable ℕ-is-discrete (range n) (remove-at 0 (labels n ℓ (b , r))))
   (λ h → γ (h m (range-member⁻¹ m n (<-succ m))))
  where
   γ : m ∈ map (label n ℓ (b , r)) (map succ (range n)) → 𝟘
   γ mm = not-less-than-itself m
           (≤-<-trans m (position m i) m (transport (_≤ position m i) e le)
             (position-bound m i))
    where
     t  = ∈-map⁻¹ (label n ℓ (b , r)) (map succ (range n)) mm
     t' = ∈-map⁻¹ succ (range n) (pr₁ (pr₂ t))

     j : ℕ
     j = pr₁ t'

     e : label n ℓ (b , r) (succ j) ＝ m
     e = ap (label n ℓ (b , r)) (pr₂ (pr₂ t')) ∙ pr₂ (pr₂ t)

     at-N : vertex (b , r) (succ j) (inl i) ＝ succ p
     at-N = ap₂ (λ x y → x +ℕ bit (lt y (succ j))) bi ri

     bit-one : ℓ (vertex (b , r) (succ j)) (inl i) ＝ ₁
     bit-one = hi (vertex (b , r) (succ j))
                (vertex-in-grid n p b r (pr₁ v) (succ j)) (inl i) at-N

     le : label n ℓ (b , r) (succ j) ≤ position m i
     le = reduced-at-most n (ℓ (vertex (b , r) (succ j))) (inl i) bit-one

 blocked-at-top : (b r : Fin n → ℕ) → Valid n p (b , r) → (i : Fin n)
                → r i ＝ m → b i ＝ 0 → door n ℓ (b , r) n ＝ ₀
 blocked-at-top b r v i ri bi =
  χ-no (⊆-decidable ℕ-is-discrete (range n) (remove-at n (labels n ℓ (b , r))))
   (λ h → γ (transport (position n i ∈_) (remove-last (label n ℓ (b , r)) n)
              (h (position n i)
                (range-member⁻¹ (position n i) n (position-bound n i)))))
  where
   γ : position n i ∈ map (label n ℓ (b , r)) (range n) → 𝟘
   γ mm = reduced-avoids n (ℓ (vertex (b , r) j)) i bit-zero (pr₂ (pr₂ t))
    where
     t = ∈-map⁻¹ (label n ℓ (b , r)) (range n) mm

     j : ℕ
     j = pr₁ t

     jn : j < n
     jn = range-member j n (pr₁ (pr₂ t))

     at-0 : vertex (b , r) j i ＝ 0
     at-0 = ap₂ (λ x y → x +ℕ bit (lt y j)) bi ri
          ∙ ap (λ c → 0 +ℕ bit c)
             (lt-no m j (λ l → not-less-than-itself m (<-≤-trans m j m l jn)))

     bit-zero : ℓ (vertex (b , r) j) i ＝ ₀
     bit-zero = lo (vertex (b , r) j) (vertex-in-grid n p b r (pr₁ v) j) i at-0

 no-door : (x : Flag n) → Valid n p (pr₁ x) → Blocked x → ¬ Boundary x → D x ＝ ₀
 no-door ((b , r) , 0)      v (inl i , ri , bi)     nbd =
  blocked-at-zero b r v i ri bi
 no-door ((b , r) , 0)      v (inr ⋆ , ri , bi)     nbd =
  𝟘-elim (nbd (refl , bi , ri))
 no-door ((b , r) , succ k) v (e , i , ri , bi)     nbd =
  transport (λ k' → door n ℓ (b , r) (succ k') ＝ ₀) (e ⁻¹)
   (blocked-at-top b r v i ri bi)

 blocked-split : (x : Flag n) → W-blocked x ＝ W-boundary x
 blocked-split x = γ (dVBd x)
  where
   γ : (d : is-decidable (Valid n p (pr₁ x) × Boundary x))
     → W-blocked x ＝ χ d & D x
   γ (inl (v , bd)) = ap (_& D x) (χ-yes (dVB x) (v , boundary-is-blocked x bd))
   γ (inr nvb)      = δ (dVB x)
    where
     δ : (d' : is-decidable (Valid n p (pr₁ x) × Blocked x)) → χ d' & D x ＝ ₀
     δ (inl (v , bl)) = no-door x v bl (λ bd → nvb (v , bd))
     δ (inr _)        = refl

\end{code}

The boundary flags and the codes of dimension m: the base at 𝟎 is
p = N − 1, the rank at 𝟎 is 0, the other ranks are the ranks of the
smaller code raised by 1, and vertex j + 1 of the flag is vertex j of
the smaller code with the coordinate N put at 𝟎. By K1 (d), the door
of the flag is the completeness of the smaller code for the labelling
restricted to that face.

\begin{code}

 lower-restricted : Lower m p ℓ̃
 lower-restricted a h i e = lo (cons (succ p) a) (extend-bound a h) (inl i) e
  where
   extend-bound : (a : Fin m → ℕ) → ((j : Fin m) → a j ≤ succ p) → (j : Fin n)
                → cons (succ p) a j ≤ succ p
   extend-bound a h (inl j) = h j
   extend-bound a h (inr ⋆) = ≤-refl (succ p)

 upper-restricted : Upper m p ℓ̃
 upper-restricted a h i e = hi (cons (succ p) a) (extend-bound a h) (inl i) e
  where
   extend-bound : (a : Fin m → ℕ) → ((j : Fin m) → a j ≤ succ p) → (j : Fin n)
                → cons (succ p) a j ≤ succ p
   extend-bound a h (inl j) = h j
   extend-bound a h (inr ⋆) = ≤-refl (succ p)

 boundary-code : (b̃ r̃ : Fin m → ℕ) → Code n
 boundary-code b̃ r̃ = cons p b̃ , cons 0 (λ i → succ (r̃ i))

 valid-extend : (b̃ r̃ : Fin m → ℕ) → Valid m p (b̃ , r̃)
              → Valid n p (boundary-code b̃ r̃)
 valid-extend b̃ r̃ (bb , rb , ri) = bounds , ranks' , injective
  where
   bounds : (i : Fin n) → cons p b̃ i ≤ p
   bounds (inl i) = bb i
   bounds (inr ⋆) = ≤-refl p

   ranks' : (i : Fin n) → cons 0 (λ i → succ (r̃ i)) i < n
   ranks' (inl i) = rb i
   ranks' (inr ⋆) = ⋆

   injective : (i j : Fin n)
    → cons 0 (λ i → succ (r̃ i)) i ＝ cons 0 (λ i → succ (r̃ i)) j → i ＝ j
   injective (inl i) (inl j) e = ap inl (ri i j (succ-lc e))
   injective (inl i) (inr ⋆) e = 𝟘-elim (positive-not-zero (r̃ i) e)
   injective (inr ⋆) (inl j) e = 𝟘-elim (positive-not-zero (r̃ j) (e ⁻¹))
   injective (inr ⋆) (inr ⋆) e = refl

 valid-restrict : (b̃ r̃ : Fin m → ℕ) → Valid n p (boundary-code b̃ r̃)
                → Valid m p (b̃ , r̃)
 valid-restrict b̃ r̃ (bb , rb , ri) = (λ i → bb (inl i)) , (λ i → rb (inl i)) ,
                                      (λ i j e →
                                        inl-lc (ri (inl i) (inl j) (ap succ e)))

 vertex-boundary : (b̃ r̃ : Fin m → ℕ) (j : ℕ)
                 → vertex (boundary-code b̃ r̃) (succ j)
                 ＝ cons (succ p) (vertex (b̃ , r̃) j)
 vertex-boundary b̃ r̃ j = dfunext fe γ
  where
   γ : vertex (boundary-code b̃ r̃) (succ j)
     ∼ cons (succ p) (vertex (b̃ , r̃) j)
   γ (inl i) = refl
   γ (inr ⋆) = refl

 label-boundary : (b̃ r̃ : Fin m → ℕ) → Valid m p (b̃ , r̃) → (j : ℕ)
                → label n ℓ (boundary-code b̃ r̃) (succ j)
                ＝ label m ℓ̃ (b̃ , r̃) j
 label-boundary b̃ r̃ ṽ j =
  ap (λ a → reduced n (ℓ a)) (vertex-boundary b̃ r̃ j)
  ∙ reduced-top m (ℓ (cons (succ p) (vertex (b̃ , r̃) j)))
     (hi (cons (succ p) (vertex (b̃ , r̃) j)) grid (inr ⋆) refl)
  where
   grid : (t : Fin n) → cons (succ p) (vertex (b̃ , r̃) j) t ≤ succ p
   grid (inl t) = vertex-in-grid m p b̃ r̃ (pr₁ ṽ) j t
   grid (inr ⋆) = ≤-refl (succ p)

 door-boundary : (b̃ r̃ : Fin m → ℕ) → Valid m p (b̃ , r̃)
               → door n ℓ (boundary-code b̃ r̃) 0 ＝ complete m ℓ̃ (b̃ , r̃)
 door-boundary b̃ r̃ ṽ =
  ap (λ L → χ (⊆-decidable ℕ-is-discrete (range n) L)) lists
  where
   lists : map (label n ℓ (boundary-code b̃ r̃)) (map succ (range n))
         ＝ labels m ℓ̃ (b̃ , r̃)
   lists = map-∘ succ (label n ℓ (boundary-code b̃ r̃)) (range n) ⁻¹
         ∙ map-ext (λ j → label n ℓ (boundary-code b̃ r̃) (succ j))
            (label m ℓ̃ (b̃ , r̃)) (range n)
             (λ j _ → label-boundary b̃ r̃ ṽ j)

 boundary-term : (b̃ r̃ : Fin m → ℕ)
               → W-boundary (boundary-code b̃ r̃ , 0)
               ＝ χ (Valid-decidable m p (b̃ , r̃)) & complete m ℓ̃ (b̃ , r̃)
 boundary-term b̃ r̃ = γ (Valid-decidable m p (b̃ , r̃))
  where
   c : Code n
   c = boundary-code b̃ r̃

   γ : (d : is-decidable (Valid m p (b̃ , r̃)))
     → W-boundary (c , 0) ＝ χ d & complete m ℓ̃ (b̃ , r̃)
   γ (inl ṽ)  = ap (_& D (c , 0))
    (χ-yes (dVBd (c , 0)) (valid-extend b̃ r̃ ṽ , refl , refl , refl))
              ∙ door-boundary b̃ r̃ ṽ
   γ (inr nṽ) = ap (_& D (c , 0))
    (χ-no (dVBd (c , 0)) (λ vb → nṽ (valid-restrict b̃ r̃ (pr₁ vb))))

\end{code}

The sum over the boundary flags is the sum of dimension m, by the
reindexings of gist.RealCohesion.KuhnCounting: the index is 0, the
base at 𝟎 is p, the rank at 𝟎 is 0, and the other ranks avoid 0.

\begin{code}

 off-boundary : (x : Flag n) → ¬ Boundary x → W-boundary x ＝ ₀
 off-boundary x nb = ap (_& D x) (χ-no (dVBd x) (λ vb → nb (pr₂ vb)))

 inner : (b̃ : Fin m → ℕ)
       → sum (λ r → W-boundary ((cons p b̃ , r) , 0)) (ranks n)
       ＝ sum (λ r̃ →
         χ (Valid-decidable m p (b̃ , r̃)) & complete m ℓ̃ (b̃ , r̃)) (ranks m)
 inner b̃ =
  sum-fixed-at-𝟎 m (range (succ m)) 0 (λ r → W-boundary ((cons p b̃ , r) , 0))
   (range-dup-free (succ m)) (inl refl)
   (λ r nr → off-boundary ((cons p b̃ , r) , 0) (λ bd → nr (pr₂ (pr₂ bd))))
  ∙ sum-avoiding-zero fe m m (λ r' → W-boundary ((cons p b̃ , cons 0 r') , 0))
     (λ r' i e → ap (_& D ((cons p b̃ , cons 0 r') , 0))
                    (χ-no (dVBd ((cons p b̃ , cons 0 r') , 0))
                      (λ vb →
                        +disjoint (pr₂ (pr₂ (pr₁ vb)) (inl i) (inr ⋆) e))))
  ∙ sum-ext _ _ (ranks m) (λ r̃ _ → boundary-term b̃ r̃)

 boundary-sum : sum W-boundary (flags n p) ＝ parity m p ℓ̃
 boundary-sum =
  sum-product W-boundary (codes n p) (range (succ n))
  ∙ sum-ext _ _ (codes n p)
     (λ c _ → sum-single (λ k → W-boundary (c , k)) (range (succ n)) 0
               (range-dup-free (succ n)) (inl refl)
               (λ k _ nk → off-boundary (c , k) (λ bd → nk (pr₁ bd))))
  ∙ sum-product (λ c → W-boundary (c , 0)) (bases n p) (ranks n)
  ∙ sum-fixed-at-𝟎 m (range (succ p)) p
     (λ b → sum (λ r → W-boundary ((b , r) , 0)) (ranks n))
     (range-dup-free (succ p)) (range-member⁻¹ p (succ p) (<-succ p))
     (λ b nb → sum-of-zeros _ (ranks n)
                (λ r _ → off-boundary ((b , r) , 0) (λ bd → nb (pr₁ (pr₂ bd)))))
  ∙ sum-ext _ _ (bases m p) (λ b̃ _ → inner b̃)
  ∙ sum-product (λ c̃ → χ (Valid-decidable m p c̃) & complete m ℓ̃ c̃)
     (bases m p) (ranks m) ⁻¹

\end{code}

The step: K2 for every code, the split of the valid flags into good and
blocked ones, K0 for the good ones (K5), and K6 for the blocked ones.

\begin{code}

 equation : parity n p ℓ ＝ parity m p ℓ̃
 equation =
  sum-ext _ _ (codes n p)
   (λ c _ → ap (V c &_) (doors-of-a-code n ℓ c ⁻¹)
            ∙ &-sum (V c) (door n ℓ c) (range (succ n)) ⁻¹)
  ∙ sum-product (λ x → V (pr₁ x) & D x) (codes n p) (range (succ n)) ⁻¹
  ∙ sum-ext _ _ (flags n p) (λ x mx → good-split x (flags-index n p x mx))
  ∙ sum-⊕ W-good W-blocked (flags n p)
  ∙ ap (_⊕ sum W-blocked (flags n p)) cancel
  ∙ sum-ext _ _ (flags n p) (λ x _ → blocked-split x)
  ∙ boundary-sum

\end{code}

The induction on n: the number of valid complete codes is odd. In
dimension 0 there is one code, and it is complete.

\begin{code}

parity-is-one : funext 𝓤₀ 𝓤₀ → (p n : ℕ) (ℓ : Labelling n) → Lower n p ℓ
              → Upper n p ℓ → parity n p ℓ ＝ ₁
parity-is-one fe p 0        ℓ lo hi = refl
parity-is-one fe p (succ m) ℓ lo hi =
 step.equation fe m p ℓ lo hi
 ∙ parity-is-one fe p m (restrict m p ℓ) (step.lower-restricted fe m p ℓ lo hi)
                                         (step.upper-restricted fe m p ℓ lo hi)

\end{code}

K7: Kuhn's lemma in every dimension. A valid complete code exists, with
a witness from the sum (sum-is-one). Put q = b. For the coordinate i,
with position j, the vertex with label j + 1 has bit 0 at i and the
vertex with label j has bit 1 at i, by K1; their indices come from the
list of labels, by membership, so the witnesses are data. The vertices
are the corners of the unit cube at b with the bits [r(t) < k].

\begin{code}

kuhn-lemma : funext 𝓤₀ 𝓤₀ → (n : ℕ) → Kuhn-Lemma n
kuhn-lemma fe n p ℓ lo hi = b , pr₁ v , γ
 where
  found : Σ c ꞉ Code n ,
            (c ∈ codes n p) × (χ (Valid-decidable n p c) & complete n ℓ c ＝ ₁)
  found =
   sum-is-one (λ c → χ (Valid-decidable n p c) & complete n ℓ c) (codes n p)
           (parity-is-one fe p n ℓ lo hi)

  c : Code n
  c = pr₁ found

  b r : Fin n → ℕ
  b = pr₁ c
  r = pr₂ c

  e : χ (Valid-decidable n p c) & complete n ℓ c ＝ ₁
  e = pr₂ (pr₂ found)

  v : Valid n p c
  v = χ-one (Valid-decidable n p c)
       (&-one-left (χ (Valid-decidable n p c)) (complete n ℓ c) e)

  complete-labels : range (succ n) ⊆ labels n ℓ c
  complete-labels =
   χ-one (⊆-decidable ℕ-is-discrete (range (succ n)) (labels n ℓ c))
                     (&-one-right (χ (Valid-decidable n p c)) (complete n ℓ c)
                       e)

  vertex-with-label : (j : ℕ) → j ≤ n → Σ k ꞉ ℕ , label n ℓ c k ＝ j
  vertex-with-label j l = pr₁ t , pr₂ (pr₂ t)
   where
    t = ∈-map⁻¹ (label n ℓ c) (range (succ n))
         (complete-labels j (range-member⁻¹ j (succ n) l))

  γ : (i : Fin n) → Σ s₀ ꞉ (Fin n → 𝟚) , Σ s₁ ꞉ (Fin n → 𝟚)
                    , (ℓ (corner b s₀) i ＝ ₀) × (ℓ (corner b s₁) i ＝ ₁)
  γ i = vertex-bits r (pr₁ t₀) , vertex-bits r (pr₁ t₁) , bit-zero , bit-one
   where
    t₀ : Σ k ꞉ ℕ , label n ℓ c k ＝ succ (position n i)
    t₀ = vertex-with-label (succ (position n i)) (position-bound n i)

    t₁ : Σ k ꞉ ℕ , label n ℓ c k ＝ position n i
    t₁ = vertex-with-label (position n i)
          (<-coarser-than-≤ (position n i) n (position-bound n i))

    bit-zero : ℓ (corner b (vertex-bits r (pr₁ t₀))) i ＝ ₀
    bit-zero = reduced-before n (ℓ (vertex c (pr₁ t₀))) i
            (transport (position n i <_) (pr₂ t₀ ⁻¹) (<-succ (position n i)))

    bit-one : ℓ (corner b (vertex-bits r (pr₁ t₁))) i ＝ ₁
    bit-one = reduced-hit n (ℓ (vertex c (pr₁ t₁))) i (pr₂ t₁)

\end{code}
