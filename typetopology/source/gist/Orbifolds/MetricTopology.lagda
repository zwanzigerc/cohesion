Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time). Orbifold gate H9 of Fable's
roadmap [1], following Fable's corrected guidance [2, Section 4 B] and
GPT-6 Astra's audits [3].

The metric topology of Rⁿ: Myers's Theorem 5.1.5
------------------------------------------------

Myers [4, Definition 5.1.4, p. 42] calls U ⊆ Rⁿ metrically open if
every x ∈ U has an ε > 0 with B(x, ε) ⊆ U, where B(x, ε) is the set of
y with Σᵢ (xᵢ − yᵢ)² < ε². His Theorem 5.1.5 says that the metrically
open subsets form a regular Hausdorff topology. Here, for every n,
including n = 0, and for open predicates with values in any universe 𝓤:

  is-metrically-open, metric-topology : Definition 5.1.4, and the
  topology it gives (metric-topology-has-local-openness);

  metric-topology-is-T₀ : two points that are not equal are separated
  by an open half-space. Postulate K, for the finite list of coordinate
  differences, gives merely an invertible coordinate difference, and O.4
  gives its sign; no unequal coordinate is chosen;

  metric-topology-is-regular : an open box around x and the open
  complement of a closed box, with cotransitivity of the order in each
  coordinate;

  theorem-5-1-5 : regular and T₀.

Proof method. Balls are compared with boxes, so that no square root
and no triangle inequality is needed [3, Section 1]: a box of radius r
lies in the ball of radius ε once n·r² ≤ ε², and a ball of radius ε
lies in the box of radius ε, because each square is at most the sum of
squares. The half-spaces and boxes are metrically open by these
comparisons. Myers proves only the case n = 1; his inequality
"x − y < 1/n" in the proof of T₀ is read "1/n < x − y" [2, Section 1,
item 4], though the proof here does not use it.

The hypotheses are Postulate O, the translation law (from Postulate
Exp) and Postulate K, all as module parameters.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Orbifolds H9 and H10: follow-up to Astra's
    readiness audits, 13 November 2026 (UTC).
    references/F04-orbifolds-h9-h10-followup.md
[3] GPT-6 Astra. Fable H9 follow-up: route and interface audit,
    13 November 2026 (UTC).
    references/A15-h9-followup-audit.txt
[4] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.MetricTopology where

open import Fin.Type
open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.UniverseEmbedding using (Lift ; lift ; lower ; Lift-≃)
open import UF.Equiv using (equiv-to-prop)
open import gist.Orbifolds.SmoothLine
open import gist.Orbifolds.SmoothOrder
open import gist.Orbifolds.SmoothOrderAlgebra

module metric-topology
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
       where

 open PropositionalTruncation pt
 open smooth-line fe pt 𝓡
 open smooth-order fe pt 𝓡
 open smooth-order-algebra fe pt 𝓡
 open import gist.Orbifolds.Topology fe pt

 module _ (O : Postulate-O) (translation : Translation-Law O) (K : Postulate-K)
        where

  open Postulate-O O
  open order-lemmas O translation
  open order-algebra O translation

\end{code}

Squared distance, balls, boxes, and Definition 5.1.4.

\begin{code}

  _−_ : R → R → R
  a − b = a +ᴿ (-ᴿ b)

  infixl 6 _−_

  squared-distance : {n : ℕ} → (Fin n → R) → (Fin n → R) → R
  squared-distance x y = ∑ (λ i → (x i − y i) ·ᴿ (x i − y i))

  is-metrically-open : {𝓤 : Universe} {n : ℕ} → Subset (Fin n → R) 𝓤 → 𝓤 ̇
  is-metrically-open {𝓤} {n} U =
   (x : Fin n → R) → x ∈ U
   → ∃ ε ꞉ R ,
       (0ᴿ < ε) × ((y : Fin n → R) → squared-distance x y < ε ·ᴿ ε → y ∈ U)

  being-metrically-open-is-prop
   : {𝓤 : Universe} {n : ℕ} (U : Subset (Fin n → R) 𝓤)
                                → is-prop (is-metrically-open U)
  being-metrically-open-is-prop U = Π₂-is-prop fe (λ _ _ → ∃-is-prop)

\end{code}

Lemmas on finite sums of squares.

\begin{code}

  ≤-is-transitive : (a b c : R) → a ≤ b → b ≤ c → a ≤ c
  ≤-is-transitive a b c l m n =
   ∥∥-rec 𝟘-is-prop (cases (λ (b<a : b < a) → l b<a) (λ (c<b : c < b) → m c<b))
    (<-is-cotransitive a c b n)

  ≤-translation : (a b c : R) → a ≤ b → a +ᴿ c ≤ b +ᴿ c
  ≤-translation a b c l m =
   l (transport₂ _<_ (+-cancel' c b) (+-cancel' c a) (translation _ _ (-ᴿ c) m))

  nonnegative-sums : {n : ℕ} (f : Fin n → R) → ((i : Fin n) → 0ᴿ ≤ f i)
                   → 0ᴿ ≤ ∑ f
  nonnegative-sums {0} f h = <-is-irreflexive 0ᴿ
  nonnegative-sums {succ n} f h =
   ≤-is-transitive 0ᴿ (0ᴿ +ᴿ 0ᴿ) _
    (λ l → <-is-irreflexive 0ᴿ (transport (_< 0ᴿ) (+-unit 0ᴿ) l))
    (≤-is-transitive _ (∑ (f ∘ suc) +ᴿ 0ᴿ) _
      (≤-translation 0ᴿ _ 0ᴿ (nonnegative-sums (f ∘ suc) (h ∘ suc)))
      (transport₂ _≤_ (+-comm 0ᴿ (∑ (f ∘ suc))) (+-comm (f 𝟎) (∑ (f ∘ suc)))
        (≤-translation 0ᴿ (f 𝟎) (∑ (f ∘ suc)) (h 𝟎))))

  term-below-sum : {n : ℕ} (f : Fin n → R) → ((i : Fin n) → 0ᴿ ≤ f i)
                 → (i : Fin n) → f i ≤ ∑ f
  term-below-sum {0} f h ()
  term-below-sum {succ n} f h 𝟎 =
   transport (_≤ ∑ (f ∘ suc) +ᴿ f 𝟎) (+-unit-left (f 𝟎))
    (≤-translation 0ᴿ _ (f 𝟎) (nonnegative-sums (f ∘ suc) (h ∘ suc)))
  term-below-sum {succ n} f h (suc i) =
   ≤-is-transitive _ _ _ (term-below-sum (f ∘ suc) (h ∘ suc) i)
    (transport₂ _≤_ (+-unit (∑ (f ∘ suc))) refl
      (transport (_≤ ∑ (f ∘ suc) +ᴿ f 𝟎) (+-comm 0ᴿ (∑ (f ∘ suc)))
        (transport (0ᴿ +ᴿ ∑ (f ∘ suc) ≤_) (+-comm (f 𝟎) (∑ (f ∘ suc)))
          (≤-translation 0ᴿ (f 𝟎) (∑ (f ∘ suc)) (h 𝟎)))))

  squares-are-nonnegative : (a : R) → 0ᴿ ≤ a ·ᴿ a
  squares-are-nonnegative a = squares-are-not-negative a

  coordinate-below-distance : {n : ℕ} (x y : Fin n → R) (i : Fin n)
                            → (x i − y i) ·ᴿ (x i − y i) ≤ squared-distance x y
  coordinate-below-distance x y =
   term-below-sum _ (λ j → squares-are-nonnegative (x j − y j))

\end{code}

Balls lie in boxes of the same radius.

\begin{code}

  ball-in-box : {n : ℕ} (x y : Fin n → R) (ε : R) → 0ᴿ < ε
              → squared-distance x y < ε ·ᴿ ε
              → (i : Fin n) → (-ᴿ ε < x i − y i) × (x i − y i < ε)
  ball-in-box x y ε lε l i =
   interval-from-square ε (x i − y i) lε
    (≤-<-is-transitive _ _ _ (coordinate-below-distance x y i) l)

\end{code}

Open half-spaces are metrically open.

\begin{code}

  module _ {𝓤 : Universe} {n : ℕ} (i : Fin n) (a c : R) where

   below : Subset (Fin n → R) 𝓤
   below w = Lift 𝓤 (a − w i < c) ,
             equiv-to-prop (Lift-≃ 𝓤 _) (<-is-prop-valued _ _)

   above : Subset (Fin n → R) 𝓤
   above w = Lift 𝓤 (c < a − w i) ,
             equiv-to-prop (Lift-≃ 𝓤 _) (<-is-prop-valued _ _)

   below-is-metrically-open : is-metrically-open below
   below-is-metrically-open w m = ∣ g , lg , γ ∣
    where
     u = a − w i
     g = c − u
     lg : 0ᴿ < g
     lg = difference-is-positive u c (lower m)
     u+g : u +ᴿ g ＝ c
     u+g = +-comm u g ∙ +-cancel u c
     γ : (z : Fin n → R) → squared-distance w z < g ·ᴿ g → z ∈ below
     γ z l = lift 𝓤 step₄
      where
       step₁ : (w i − z i) +ᴿ u < g +ᴿ u
       step₁ = translation _ _ u (pr₂ (ball-in-box w z g lg l i))
       step₂ : u +ᴿ (w i − z i) < u +ᴿ g
       step₂ = transport₂ _<_ (+-comm _ u) (+-comm g u) step₁
       step₃ : u +ᴿ (w i − z i) < c
       step₃ = transport (u +ᴿ (w i − z i) <_) u+g step₂
       step₄ : a − z i < c
       step₄ = transport (_< c) (differences-compose (z i) (w i) a) step₃

   above-is-metrically-open : is-metrically-open above
   above-is-metrically-open w m = ∣ g , lg , γ ∣
    where
     u = a − w i
     g = u − c
     lg : 0ᴿ < g
     lg = difference-is-positive c u (lower m)
     u-g : u +ᴿ (-ᴿ g) ＝ c
     u-g = ap (u +ᴿ_)
      (negation-of-sum u (-ᴿ c) ∙ ap ((-ᴿ u) +ᴿ_) (negation-is-involutive c))
         ∙ (+-assoc u (-ᴿ u) c)⁻¹ ∙ ap (_+ᴿ c) (+-inverse u) ∙ +-unit-left c
     γ : (z : Fin n → R) → squared-distance w z < g ·ᴿ g → z ∈ above
     γ z l = lift 𝓤 step₄
      where
       step₁ : (-ᴿ g) +ᴿ u < (w i − z i) +ᴿ u
       step₁ = translation _ _ u (pr₁ (ball-in-box w z g lg l i))
       step₂ : u +ᴿ (-ᴿ g) < u +ᴿ (w i − z i)
       step₂ = transport₂ _<_ (+-comm _ u) (+-comm _ u) step₁
       step₃ : c < u +ᴿ (w i − z i)
       step₃ = transport (_< u +ᴿ (w i − z i)) u-g step₂
       step₄ : c < a − z i
       step₄ = transport (c <_) (differences-compose (z i) (w i) a) step₃

\end{code}

The topology.

\begin{code}

  squares-of-smaller-positives : (c e : R) → 0ᴿ < c → c < e → c ·ᴿ c < e ·ᴿ e
  squares-of-smaller-positives c e lc l =
   <-is-transitive _ _ _
    (transport₂ _<_ refl (·-comm e c)
      (products-with-positive-factor-preserve-order c e c lc l))
    (products-with-positive-factor-preserve-order c e e
      (<-is-transitive _ _ _ lc l) l)

  metric-topology : (𝓤 : Universe) (n : ℕ) → Topology (Fin n → R) 𝓤
  metric-topology 𝓤 n = record
   { is-open = λ U → Lift (𝓤 ⁺) (is-metrically-open U)
    ; being-open-is-prop =
     λ U → equiv-to-prop (Lift-≃ (𝓤 ⁺) _) (being-metrically-open-is-prop U)
    ; openness-is-extensional =
      λ A B A⊆B B⊆A oA → lift (𝓤 ⁺)
       (λ x xB → ∥∥-functor (λ (ε , lε , f) → ε , lε , (λ y l → A⊆B y (f y l)))
                  (lower oA x (B⊆A x xB)))
    ; full-is-open = lift (𝓤 ⁺) (λ x _ → ∣ 1ᴿ , one-is-positive , (λ _ _ → ⋆) ∣)
    ; ∩-is-open =
      λ U V oU oV → lift (𝓤 ⁺)
       (λ x (xU , xV) →
         ∥∥-functor₂
          (λ (ε₁ , l₁ , f₁) (ε₂ , l₂ , f₂) →
            let (c , lc , c<ε₁ , c<ε₂) = positive-below-two K ε₁ ε₂ l₁ l₂ in
            c , lc ,
            (λ y l → f₁ y (<-is-transitive _ _ _ l
                            (squares-of-smaller-positives c ε₁ lc c<ε₁)) ,
                     f₂ y (<-is-transitive _ _ _ l
                            (squares-of-smaller-positives c ε₂ lc c<ε₂))))
          (lower oU x xU) (lower oV x xV))
    ; ⋃-is-open =
      λ U o → lift (𝓤 ⁺)
       (λ x m → ∥∥-rec ∃-is-prop
                 (λ (j , xUj) → ∥∥-functor
                   (λ (ε , lε , f) → ε , lε , (λ y l → ∣ j , f y l ∣))
                                  (lower (o j) x xUj))
                 m)
    }

  metric-topology-has-local-openness : {𝓤 : Universe} {n : ℕ}
                                     → has-local-openness (metric-topology 𝓤 n)
  metric-topology-has-local-openness A l = lift _
   (λ x xA → ∥∥-rec ∃-is-prop
              (λ (U , oU , xU , U⊆A) →
                ∥∥-functor (λ (ε , lε , f) → ε , lε , (λ y m → U⊆A y (f y m)))
                 (lower oU x xU))
              (l x xA))

\end{code}

T₀: Postulate K on the coordinate differences.

\begin{code}

  equal-from-zero-difference : (a b : R) → a − b ＝ 0ᴿ → a ＝ b
  equal-from-zero-difference a b p =
   a                    ＝⟨ (+-cancel b a)⁻¹ ⟩
   (a − b) +ᴿ b         ＝⟨ ap (_+ᴿ b) p ⟩
   0ᴿ +ᴿ b              ＝⟨ +-unit-left b ⟩
   b                    ∎

  metric-topology-is-T₀ : {𝓤 : Universe} {n : ℕ} → is-T₀ (metric-topology 𝓤 n)
  metric-topology-is-T₀ {𝓤} {n} x y ν =
   ∥∥-rec ∥∥-is-prop
    (λ (i , u) →
      ∥∥-functor
       (cases (λ (d<0 : x i − y i < 0ᴿ) → inl (separate-above i d<0))
              (λ (0<d : 0ᴿ < x i − y i) → inl (separate-below i 0<d)))
       (nonzero-elements-are-comparable (x i − y i)
         (λ p → zero-is-not-one
                  ((·-zero (pr₁ u))⁻¹ ∙ ap (pr₁ u ·ᴿ_) (p ⁻¹) ∙ pr₂ u))))
    (pr₂ K n (λ i → x i − y i)
      (λ h →
        ν (dfunext fe (λ i → equal-from-zero-difference (x i) (y i) (h i)))))
   where
    zero-difference : (i : Fin n) → x i − x i ＝ 0ᴿ
    zero-difference i = +-inverse (x i)

    separate-below : (i : Fin n) → 0ᴿ < x i − y i
                   → ∃ U ꞉ Subset (Fin n → R) 𝓤 ,
                        Topology.is-open (metric-topology 𝓤 n) U × x ∈ U
                         × ¬ (y ∈ U)
    separate-below i l =
     ∣ below i (x i) (x i − y i) ,
       lift (𝓤 ⁺) (below-is-metrically-open i (x i) (x i − y i)) ,
       lift 𝓤 (transport (_< x i − y i) ((zero-difference i)⁻¹) l) ,
       (λ m → <-is-irreflexive _ (lower m)) ∣

    separate-above : (i : Fin n) → x i − y i < 0ᴿ
                   → ∃ U ꞉ Subset (Fin n → R) 𝓤 ,
                        Topology.is-open (metric-topology 𝓤 n) U × x ∈ U
                         × ¬ (y ∈ U)
    separate-above i l =
     ∣ above i (x i) (x i − y i) ,
       lift (𝓤 ⁺) (above-is-metrically-open i (x i) (x i − y i)) ,
       lift 𝓤 (transport (x i − y i <_) ((zero-difference i)⁻¹) l) ,
       (λ m → <-is-irreflexive _ (lower m)) ∣

\end{code}

Finite intersections, finite disjunctions, and sums of bounded terms.

\begin{code}

  finite-intersections-are-open
   : {𝓧 𝓤 : Universe} {X : 𝓧 ̇ } (T : Topology X 𝓤) {n : ℕ}
     (U : Fin n → Subset X 𝓤)
   → ((i : Fin n) → Topology.is-open T (U i))
   → Topology.is-open T (λ x → ((i : Fin n) → x ∈ U i) ,
                              Π-is-prop fe (λ i → ∈-is-prop x (U i)))
  finite-intersections-are-open T {0} U o =
   Topology.openness-is-extensional T full _ (λ x _ → λ ()) (λ x _ → ⋆)
    (Topology.full-is-open T)
  finite-intersections-are-open T {succ n} U o =
   Topology.openness-is-extensional T _ _
    (λ x (h , u) → λ { (suc i) → h i ; 𝟎 → u })
    (λ x f → (λ i → f (suc i)) , f 𝟎)
    (Topology.∩-is-open T _ (U 𝟎)
      (finite-intersections-are-open T (U ∘ suc) (o ∘ suc)) (o 𝟎))

  finite-choice-of-sides
   : {𝓦 𝓦' : Universe} {n : ℕ} (A : Fin n → 𝓦 ̇ ) (B : Fin n → 𝓦' ̇ )
   → ((i : Fin n) → A i ∨ B i)
   → ((i : Fin n) → A i) ∨ (∃ i ꞉ Fin n , B i)
  finite-choice-of-sides {𝓦} {𝓦'} {0} A B h = ∣ inl (λ ()) ∣
  finite-choice-of-sides {𝓦} {𝓦'} {succ n} A B h =
   ∥∥-rec ∥∥-is-prop
    (cases (λ (a-rest : (i : Fin n) → A (suc i)) →
              ∥∥-functor
               (cases (λ a₀ → inl (λ { (suc i) → a-rest i ; 𝟎 → a₀ }))
                      (λ b₀ → inr ∣ 𝟎 , b₀ ∣))
               (h 𝟎))
           (λ b-rest → ∣ inr (∥∥-functor (λ (i , b) → suc i , b) b-rest) ∣))
    (finite-choice-of-sides (A ∘ suc) (B ∘ suc) (h ∘ suc))

  ι-successor-is-positive : (n : ℕ) → 0ᴿ < ι n +ᴿ 1ᴿ
  ι-successor-is-positive 0 =
   transport (0ᴿ <_) ((+-unit-left 1ᴿ)⁻¹) one-is-positive
  ι-successor-is-positive (succ n) =
   sums-of-positives-are-positive _ _ (ι-successor-is-positive n)
    one-is-positive

  ∑-bound : {n : ℕ} (f : Fin n → R) (c : R) → ((i : Fin n) → f i < c)
          → ∑ f ≤ ι n ·ᴿ c
  ∑-bound {0} f c h =
   transport (0ᴿ ≤_) ((·-zero-left c)⁻¹) (<-is-irreflexive 0ᴿ)
  ∑-bound {succ n} f c h =
   ≤-is-transitive _ _ _
    (≤-translation _ _ (f 𝟎) (∑-bound (f ∘ suc) c (h ∘ suc)))
    (transport (ι n ·ᴿ c +ᴿ f 𝟎 ≤_)
      ((ap (ι n ·ᴿ c +ᴿ_) (·-unit-left c))⁻¹
       ∙ (distributivity-right (ι n) 1ᴿ c)⁻¹)
      (<-gives-≤ _ _
        (transport₂ _<_ (+-comm (f 𝟎) (ι n ·ᴿ c)) (+-comm c (ι n ·ᴿ c))
         (translation (f 𝟎) c (ι n ·ᴿ c) (h 𝟎)))))

\end{code}

Boxes inside balls: a box of radius r lies in the ball of radius ε once
r² < ε²/(n + 1).

\begin{code}

  box-radius : (n : ℕ) (ε : R) → 0ᴿ < ε
             → Σ r ꞉ R , (0ᴿ < r)
                       × ((x y : Fin n → R)
                            →
                            ((i : Fin n) → (-ᴿ r < x i − y i) × (x i − y i < r))
                            → squared-distance x y < ε ·ᴿ ε)
  box-radius n ε lε = r , lr , γ
   where
    s = ι n +ᴿ 1ᴿ
    ls : 0ᴿ < s
    ls = ι-successor-is-positive n
    w = pr₁ (positive-elements-are-invertible K s ls)
    ws : w ·ᴿ s ＝ 1ᴿ
    ws = pr₂ (positive-elements-are-invertible K s ls)
    lw : 0ᴿ < w
    lw = inverses-of-positive-elements-are-positive K s ls
    ε² = ε ·ᴿ ε
    lε² : 0ᴿ < ε²
    lε² = products-of-positives-are-positive ε ε lε lε
    c = ε² ·ᴿ w
    lc : 0ᴿ < c
    lc = products-of-positives-are-positive ε² w lε² lw
    ιw<1 : ι n ·ᴿ w < 1ᴿ
    ιw<1 = transport (ι n ·ᴿ w <_) (·-comm s w ∙ ws)
            (products-with-positive-factor-preserve-order (ι n) s w lw
              (transport₂ _<_ (+-unit-left (ι n)) (+-comm 1ᴿ (ι n))
                (translation 0ᴿ 1ᴿ (ι n) one-is-positive)))
    ιc<ε² : ι n ·ᴿ c < ε²
    ιc<ε² = transport₂ _<_
             (·-assoc (ι n) w ε² ∙ ap (ι n ·ᴿ_) (·-comm w ε²))
             (·-unit-left ε²)
             (products-with-positive-factor-preserve-order (ι n ·ᴿ w) 1ᴿ ε² lε²
               ιw<1)
    ρ = positive-with-small-square K c lc
    r = pr₁ ρ
    lr = pr₁ (pr₂ ρ)
    r²<c : r ·ᴿ r < c
    r²<c = pr₂ (pr₂ ρ)
    γ : (x y : Fin n → R)
      → ((i : Fin n) → (-ᴿ r < x i − y i) × (x i − y i < r))
      → squared-distance x y < ε²
    γ x y b = ≤-<-is-transitive _ _ _
               (∑-bound (λ i → (x i − y i) ·ᴿ (x i − y i)) c
                 (λ i → <-is-transitive _ _ _
                          (square-from-interval r (x i − y i) (pr₁ (b i))
                            (pr₂ (b i)))
                          r²<c))
               ιc<ε²

\end{code}

Regularity: inside a ball B(x, ε) ⊆ U, take a box of radius r inside the
ball and a smaller radius h < r. The open box V of radius h around x and
the set G of points outside the closed box of radius h are disjoint, and
cotransitivity in each coordinate puts every point in G or in the box of
radius r, hence in U.

\begin{code}

  metric-topology-is-regular : {𝓤 : Universe} {n : ℕ}
                             → is-regular (metric-topology 𝓤 n)
  metric-topology-is-regular {𝓤} {n} U oU x xU =
   ∥∥-functor γ (lower oU x xU)
   where
    T = metric-topology 𝓤 n

    below' above' : Fin n → R → Subset (Fin n → R) 𝓤
    below' i c = below {𝓤} i (x i) c
    above' i c = above {𝓤} i (x i) c

    below'-is-open : (i : Fin n) (c : R) → Topology.is-open T (below' i c)
    below'-is-open i c = lift (𝓤 ⁺) (below-is-metrically-open {𝓤} i (x i) c)

    above'-is-open : (i : Fin n) (c : R) → Topology.is-open T (above' i c)
    above'-is-open i c = lift (𝓤 ⁺) (above-is-metrically-open {𝓤} i (x i) c)

    γ : (Σ ε ꞉ R ,
          (0ᴿ < ε) × ((y : Fin n → R) → squared-distance x y < ε ·ᴿ ε → y ∈ U))
      → Σ V ꞉ Subset (Fin n → R) 𝓤 , Σ G ꞉ Subset (Fin n → R) 𝓤 ,
           Topology.is-open T V × Topology.is-open T G × x ∈ V
         × ((y : Fin n → R) → y ∈ G → y ∈ V → 𝟘 {𝓤₀})
         × ((y : Fin n → R) → (y ∈ G) ∨ (y ∈ U))
    γ (ε , lε , ball-in-U) = V , G , oV , oG , xV , disjoint , cover
     where
      ρ = box-radius n ε lε
      r = pr₁ ρ
      lr = pr₁ (pr₂ ρ)
      η = positive-below-two K r r lr lr
      h = pr₁ η
      lh : 0ᴿ < h
      lh = pr₁ (pr₂ η)
      h<r : h < r
      h<r = pr₁ (pr₂ (pr₂ η))

      box : Fin n → Subset (Fin n → R) 𝓤
      box i = below' i h ∩ above' i (-ᴿ h)

      V : Subset (Fin n → R) 𝓤
      V y = ((i : Fin n) → y ∈ box i) , Π-is-prop fe (λ i → ∈-is-prop y (box i))

      oV : Topology.is-open T V
      oV = finite-intersections-are-open T box
            (λ i → Topology.∩-is-open T (below' i h) (above' i (-ᴿ h))
                    (below'-is-open i h) (above'-is-open i (-ᴿ h)))

      outside : Fin n → Subset (Fin n → R) 𝓤
      outside i y = ((y ∈ above' i h) ∨ (y ∈ below' i (-ᴿ h))) , ∥∥-is-prop

      G : Subset (Fin n → R) 𝓤
      G y = (∃ i ꞉ Fin n , y ∈ outside i) , ∃-is-prop

      oG : Topology.is-open T G
      oG = metric-topology-has-local-openness G
            (λ y → ∥∥-rec ∃-is-prop
                    (λ (i , o) →
                      ∥∥-functor
                       (cases (λ a → above' i h , above'-is-open i h ,
                                     a , (λ z m → ∣ i , ∣ inl m ∣ ∣))
                              (λ b → below' i (-ᴿ h) , below'-is-open i (-ᴿ h) ,
                                     b , (λ z m → ∣ i , ∣ inr m ∣ ∣)))
                       o))

      zero-difference : (i : Fin n) → x i − x i ＝ 0ᴿ
      zero-difference i = +-inverse (x i)

      xV : x ∈ V
      xV i = lift 𝓤 (transport (_< h) ((zero-difference i)⁻¹) lh) ,
             lift 𝓤 (transport (-ᴿ h <_) ((zero-difference i)⁻¹)
                       (negation-of-positive-is-negative h lh))

      disjoint : (y : Fin n → R) → y ∈ G → y ∈ V → 𝟘 {𝓤₀}
      disjoint y yG yV =
       ∥∥-rec 𝟘-is-prop
        (λ (i , o) → ∥∥-rec 𝟘-is-prop
                      (cases (λ a →
                        <-is-asymmetric _ _ (lower a) (lower (pr₁ (yV i))))
                             (λ b → <-is-asymmetric _ _ (lower b)
                                     (lower (pr₂ (yV i)))))
                      o)
        yG

      cover : (y : Fin n → R) → (y ∈ G) ∨ (y ∈ U)
      cover y =
       ∥∥-functor
        (cases (λ all-inside → inr (ball-in-U y (pr₂ (pr₂ ρ) x y all-inside)))
               (λ some-outside → inl some-outside))
        (finite-choice-of-sides
          (λ i → (-ᴿ r < x i − y i) × (x i − y i < r))
          (λ i → y ∈ outside i)
          side)
       where
        side : (i : Fin n)
             → ((-ᴿ r < x i − y i) × (x i − y i < r)) ∨ (y ∈ outside i)
        side i =
         ∥∥-rec ∥∥-is-prop
          (cases (λ (d<r : x i − y i < r) →
                    ∥∥-functor
                     (cases
                       (λ (d<-h : x i − y i < -ᴿ h) → inr ∣ inr (lift 𝓤 d<-h) ∣)
                            (λ (-r<d : -ᴿ r < x i − y i) → inl (-r<d , d<r)))
                     (<-is-cotransitive (-ᴿ h) (-ᴿ r) (x i − y i)
                       (negation-reverses-order h r h<r)))
                 (λ (h<d : h < x i − y i) → ∣ inr ∣ inl (lift 𝓤 h<d) ∣ ∣))
          (<-is-cotransitive r h (x i − y i) h<r)

  theorem-5-1-5 : {𝓤 : Universe} {n : ℕ}
                → is-regular-Hausdorff (metric-topology 𝓤 n)
  theorem-5-1-5 = metric-topology-is-regular , metric-topology-is-T₀

\end{code}
