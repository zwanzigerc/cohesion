Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time); the scope of the finite
subcover made precise later that day, in the third part of the
consolidation [5]; its attribution to Myers's statements corrected at
the integration of the Weil comparison, the same night [6]. Orbifold
gate H10 of Fable's roadmap [1], for the target T5b.

Finite subcovers of crisp covers of crisp Dubuc–Penon compact subsets
---------------------------------------------------------------------

The composite of Myers's Remark 6.2.16 [2], for crisp subsets and
crisp covers under the stated hypotheses, in finite-indexed-list form,
as T5b uses it [3, Section 5; 4, Section E; 6]. The proof uses the
argument of Corollary 6.2.14 followed by a crisp decision and finite
witness selection; neither Corollary 6.2.14 nor Proposition 6.2.15 is
stated separately, and refinement subcompactness is not defined here.
The conclusion is a finite indexed list of members of the cover, in
which an index or an open may occur more than once, not a finite set of
opens. Let X carry a regular topology
with a basis B : ℕ → Subset X 𝓤, and let S be a subset of X whose type
of points is Dubuc–Penon compact. For a crisp family V of opens indexed
by a crisp I and covering S, with S, B, V crisp:

  refinement-predicate S B V n : merely some V i contains the part of
  the n-th basic open that lies in S. It mentions only S, B and V, so
  it is crisp; it mentions no proof of openness, of the basis property
  or of compactness;

  crisp-DP-compact-subsets-have-finite-subcovers : merely a finite list
  F of indices with S ⊆ ⋃_{i ∈ F} V i.

Proof. The basic opens on which the refinement predicate holds cover S
and are Penon open (Lemma 6.2.7, from regularity), so Theorem 6.2.13
bounds their indices by some N. Crisp excluded middle decides the
crisp refinement predicate at every natural number (the library's
decide-at, through crisp-subtypes-of-ℕ-are-decidable); a recursion on
N, inside the proposition to be proved, keeps one member V i for each
n < N at which the predicate holds, using only the mere existence of
that member, so only finitely many mere witnesses are opened. No
countable choice and no ordinary excluded middle is used.

The hypotheses are Postulates O, Exp and K, Postulate E at 𝓤, and crisp
excluded middle at 𝓤 (crisp, as in CrispCoverFiniteness).

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
[3] GPT-6 Astra. DP properness implies the replacement over the
    five-item core, 11 November 2026.
    references/A02-dp-properness-implies-replacement.txt
[4] GPT-6 Astra. H10 T5b implementation preflight, 13 November 2026
    (UTC).
    references/A24-t5b-preflight.txt
[5] GPT-6 Astra. Consolidation implementation, third release
    (OPUS-CONSOLIDATION-RELEASE-03), 13 November 2026: the scope of the
    statements, made precise.
    references/A33-consolidation-release-03.txt
[6] Disposition R2 of Claude Fable 5.2's final packaging minors, in
    root's review of the r3 delivery, 13 November 2026, as carried into
    GPT-6 Astra. Release of WG8, the integration of the Weil
    comparison, 13 November 2026 (local time).
    references/A64-r3-final-minor-dispositions.txt
    references/A49-weil-release-wg8.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.FiniteSubcovers
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
       where

open import Fin.Type
open import Naturals.Order using (_≤ℕ_ ; ≤-split)
open import Naturals.Properties using (succ-lc)
open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import gist.CohesiveApartness.Flat using (Crisp-EM)
open import gist.Orbifolds.SmoothOrder
open import gist.Orbifolds.CoveringProperty

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open smooth-order fe pt 𝓡
open covering-property fe pt 𝓡
open import gist.Orbifolds.Topology fe pt
open import gist.Orbifolds.DubucPenon fe pt
open import gist.Orbifolds.CoverFiniteness fe pt using (is-Penon-open)
open import gist.Orbifolds.CrispCoverFiniteness fe pt {𝓤₀}
 using (crisp-subtypes-of-ℕ-are-decidable)

\end{code}

The refinement predicate, and the finite list from a bound.

\begin{code}

refinement-predicate
 : {𝓤 : Universe} {X : 𝓤 ̇ } (S : X → 𝓤 ̇ ) (B : ℕ → Subset X 𝓤)
                       {I : 𝓤 ̇ } (V : I → Subset X 𝓤) → ℕ → 𝓤 ̇
refinement-predicate {𝓤} {X} S B {I} V n =
 ∥ Σ i ꞉ I , ((x : X) → S x → x ∈ B n → x ∈ V i) ∥

finite-subcovers-from-bounds
 : {@♭ 𝓤 : Universe} (@♭ cem : Crisp-EM 𝓤)
 → {@♭ X : 𝓤 ̇ } (@♭ S : X → 𝓤 ̇ ) (@♭ B : ℕ → Subset X 𝓤)
   {@♭ I : 𝓤 ̇ } (@♭ V : I → Subset X 𝓤)
 → ∃ N ꞉ ℕ , ((x : X) → S x
             → ∃ n ꞉ ℕ , (n <ℕ N) × refinement-predicate S B V n × x ∈ B n)
 → ∃ m ꞉ ℕ , Σ F ꞉ (Fin m → I) , ((x : X) → S x → ∃ j ꞉ Fin m , x ∈ V (F j))
finite-subcovers-from-bounds {𝓤} cem {X} S B {I} V =
 ∥∥-rec ∃-is-prop
  (λ (N , h) →
    ∥∥-functor
     (λ (m , F , c) →
       m , F ,
        (λ x s → ∥∥-rec ∃-is-prop (λ (n , l , j , b) → c n l j x s b) (h x s)))
     (lists N))
 where
  Jn : ℕ → 𝓤 ̇
  Jn = refinement-predicate S B V

  decide : (n : ℕ) → is-decidable (Jn n)
  decide = crisp-subtypes-of-ℕ-are-decidable cem (refinement-predicate S B V)
            (λ n → ∥∥-is-prop)

  Covers-Below : ℕ → (m : ℕ) → (Fin m → I) → 𝓤 ̇
  Covers-Below N m F = (n : ℕ) → n <ℕ N → Jn n → (x : X) → S x → x ∈ B n
                     → ∃ j ꞉ Fin m , x ∈ V (F j)

  lists : (N : ℕ) → ∃ m ꞉ ℕ , Σ F ꞉ (Fin m → I) , Covers-Below N m F
  lists 0 = ∣ 0 , (λ ()) , (λ n l → 𝟘-elim l) ∣
  lists (succ N) = ∥∥-rec ∃-is-prop step (lists N)
   where
    below-or-equal : (n : ℕ) → n <ℕ succ N → (n <ℕ N) + (n ＝ N)
    below-or-equal n l =
     cases inl (λ p → inr (succ-lc p)) (≤-split (succ n) N l)

    step : (Σ m ꞉ ℕ , Σ F ꞉ (Fin m → I) , Covers-Below N m F)
         → ∃ m ꞉ ℕ , Σ F ꞉ (Fin m → I) , Covers-Below (succ N) m F
    step (m , F , c) =
     cases
      (λ (jN : Jn N) →
        ∥∥-functor
         (λ (i , inc) →
           succ m , (λ { (suc j) → F j ; 𝟎 → i }) ,
           (λ n l jn x s b →
             cases (λ l' → ∥∥-functor (λ (j , v) → suc j , v) (c n l' jn x s b))
                   (λ (p : n ＝ N) →
                     ∣ 𝟎 , inc x s (transport (λ - → x ∈ B -) p b) ∣)
                   (below-or-equal n l)))
         jN)
      (λ (¬jN : ¬ Jn N) →
        ∣ m , F ,
          (λ n l jn x s b →
            cases (λ l' → c n l' jn x s b)
                  (λ (p : n ＝ N) → 𝟘-elim (¬jN (transport Jn p jn)))
                  (below-or-equal n l)) ∣)
      (decide N)

\end{code}

Finite subcovers.

\begin{code}

module _ (O : Postulate-O) (Exp : Postulate-Exp O) (K : Postulate-K)
         {@♭ 𝓤 : Universe} (E : Postulate-E O Exp K 𝓤)
       where

 crisp-DP-compact-subsets-have-finite-subcovers
  : (@♭ cem : Crisp-EM 𝓤)
  → {@♭ X : 𝓤 ̇ } (T : Topology X 𝓤) → is-regular T
  → (@♭ B : ℕ → Subset X 𝓤) → is-basis T B
  → (@♭ S : X → 𝓤 ̇ ) → ((x : X) → is-prop (S x))
  → is-DP-compact (Σ x ꞉ X , S x)
  → (@♭ I : 𝓤 ̇ ) (@♭ V : I → Subset X 𝓤)
  → ((i : I) → Topology.is-open T (V i))
  → ((x : X) → S x → ∃ i ꞉ I , x ∈ V i)
  → ∃ m ꞉ ℕ , Σ F ꞉ (Fin m → I) , ((x : X) → S x → ∃ j ꞉ Fin m , x ∈ V (F j))
 crisp-DP-compact-subsets-have-finite-subcovers cem {X} T r B b S S-is-prop c I
  V oV cover =
  finite-subcovers-from-bounds cem S B V
   (∥∥-functor
     (λ (N , h) → N , (λ x s → h (x , s)))
     (theorem-6-2-13 O Exp K E (Σ x ꞉ X , S x) c U
       (λ n z → ×-is-prop ∥∥-is-prop (∈-is-prop (pr₁ z) (B n)))
       U-is-Penon-open U-covers))
  where
   U : ℕ → (Σ x ꞉ X , S x) → 𝓤 ̇
   U n z = refinement-predicate S B V n × pr₁ z ∈ B n

   U-is-Penon-open : (n : ℕ) → is-Penon-open (U n)
   U-is-Penon-open n (x , s) (j , xb) (y , t) =
    ∥∥-functor
     (cases (λ (xy : x ≠ y) → inl (λ p → xy (ap pr₁ p)))
            (λ yb → inr (j , yb)))
     (opens-of-regular-spaces-are-Penon-open T r (B n) (pr₁ b n) x xb y)

   U-covers : (z : Σ x ꞉ X , S x) → ∃ n ꞉ ℕ , U n z
   U-covers (x , s) =
    ∥∥-rec ∃-is-prop
     (λ (i , xV) →
       ∥∥-functor
        (λ (n , xb , inc) → n , ∣ i , (λ y _ yb → inc y yb) ∣ , xb)
        (pr₂ b (V i) (oV i) x xV))
     (cover x s)

\end{code}
