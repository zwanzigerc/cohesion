Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Finite counting modulo 2 for Kuhn's lemma in every dimension: steps K0
and K2 of Claude Fable 5.2's route [1], revision 3, which GPT-6 Astra
audited and released on 13 November 2026 UTC. The rest of the route is
in gist.RealCohesion.KuhnLemmaGeneral.

The finite types of the route are given by lists: a list without
repetitions that contains every element of interest. Sums are taken
modulo 2, in 𝟚 with exclusive or.

 * K0, the cancellation lemma (cancellation). Let T be a map on a type
   with decidable equality, and w a function to 𝟚. If a list xs has no
   repetitions, is closed under T, T (T x) = x and w (T x) = w x for x
   in xs, and T x ≠ x whenever w x = 1, then the sum of w over xs is 0.
   The proof removes pairs: the head x and, if T x ≠ x, the element
   T x; their terms cancel, and the rest is again closed under T. This
   is a genuine pairing of the terms, not the invariance of the sum
   under the bijection T, which cancels nothing.

 * The pigeonhole principle for lists (pigeonhole): if S has no
   repetitions and every element of S is in ys, then length S ≤
   length ys.

 * The general form of K2 (door-count): for lists xs and S, with S
   without repetitions and length xs = length S + 1, the number of
   positions k such that every element of S is still in xs with its
   k-th entry removed is odd if and only if every element of S is in
   xs and some entry of xs is not in S. With S = 0, …, n − 1 and the
   n + 1 reduced labels of a simplex, all at most n, this is K2: a
   simplex has an odd number of doors if and only if it is complete.
   The proof is by induction on xs, with the pigeonhole principle
   where a list would be too short.

 * Sums over the functions from Fin m to the entries of a list
   (functions), over products, and the reindexings that step K6 needs.

Isabelle's Brouwer_Fixpoint.thy [2] is a mathematical reference here,
not a source of code: kuhn_counting_lemma (lines 296–326 of the pinned
file) for the idea of K0, and the second half of kuhn_complete_lemma
(lines 327–412) for the case division of K2, which the proof of
door-count replaces by an induction. Isabelle counts finite sets; here
the counts are sums modulo 2 over lists.

[1] Claude Fable 5.2. Kuhn's lemma in every dimension: the finite
    route. Revision 3, 13 November 2026, audited by GPT-6 Astra.
    references/F10-kuhn-finite-route-rev3.md

[2] Brouwer_Fixpoint.thy of Isabelle/HOL (src/HOL/Analysis), at
    revision 87958a2e5f99606413f8c4f3af90935a5ac33110 of the Isabelle
    mirror, by John Harrison (from HOL Light), translated to
    Isabelle/HOL by Robert Himmelmann, with LCP. See
    ISABELLE-COPYRIGHT in this folder.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.KuhnCounting where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import MLTT.List using (List ; [] ; _∷_ ; length ; map ; _++_ ; concat ;
                             course-of-values-induction-on-length)
open import MLTT.Two-Properties
 using (_⊕_ ; zero-is-not-one ; different-from-₁-equal-₀ ;
        ⊕-assoc)
open import Fin.Type
open import Naturals.Order
open import Naturals.Properties using (succ-lc ; positive-not-zero)
open import Notation.Order
open import NotionsOfDecidability.Decidable using (×-preserves-decidability ;
                                                   +-preserves-decidability)
open import UF.Base using (ap₂)
open import UF.DiscreteAndSeparated using (is-discrete)
open import UF.FunExt
open import gist.RealCohesion.KuhnLemma using (xor-right-unit ; xor-is-one)

\end{code}

Bits from decisions, and an exchange law for exclusive or.

\begin{code}

ite : {A : 𝓤 ̇ } {X : 𝓥 ̇ } → is-decidable A → X → X → X
ite (inl _) x y = x
ite (inr _) x y = y

ite-yes : {A : 𝓤 ̇ } {X : 𝓥 ̇ } (d : is-decidable A) {x y : X} → A
        → ite d x y ＝ x
ite-yes (inl _) a = refl
ite-yes (inr u) a = 𝟘-elim (u a)

ite-no : {A : 𝓤 ̇ } {X : 𝓥 ̇ } (d : is-decidable A) {x y : X} → ¬ A
       → ite d x y ＝ y
ite-no (inl a) u = 𝟘-elim (u a)
ite-no (inr _) u = refl

χ : {A : 𝓤 ̇ } → is-decidable A → 𝟚
χ d = ite d ₁ ₀

χ-yes : {A : 𝓤 ̇ } (d : is-decidable A) → A → χ d ＝ ₁
χ-yes d = ite-yes d

χ-no : {A : 𝓤 ̇ } (d : is-decidable A) → ¬ A → χ d ＝ ₀
χ-no d = ite-no d

χ-one : {A : 𝓤 ̇ } (d : is-decidable A) → χ d ＝ ₁ → A
χ-one (inl a) e = a
χ-one (inr u) e = 𝟘-elim (zero-is-not-one e)

χ-↔ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (d : is-decidable A) (e : is-decidable B)
    → (A → B) → (B → A) → χ d ＝ χ e
χ-↔ (inl a) (inl b) f g = refl
χ-↔ (inl a) (inr v) f g = 𝟘-elim (v (f a))
χ-↔ (inr u) (inl b) f g = 𝟘-elim (u (g b))
χ-↔ (inr u) (inr v) f g = refl

xor-left-swap : (a b c : 𝟚) → a ⊕ (b ⊕ c) ＝ b ⊕ (a ⊕ c)
xor-left-swap ₀ ₀ c = refl
xor-left-swap ₀ ₁ c = refl
xor-left-swap ₁ ₀ c = refl
xor-left-swap ₁ ₁ c = refl

\end{code}

Membership, inclusion and lists without repetitions. Membership is
defined by recursion on the list.

\begin{code}

_∈_ : {X : 𝓤 ̇ } → X → List X → 𝓤 ̇
x ∈ []       = 𝟘
x ∈ (y ∷ ys) = (x ＝ y) ∔ (x ∈ ys)

_⊆_ : {X : 𝓤 ̇ } → List X → List X → 𝓤 ̇
_⊆_ {𝓤} {X} xs ys = (z : X) → z ∈ xs → z ∈ ys

dup-free : {X : 𝓤 ̇ } → List X → 𝓤 ̇
dup-free []       = 𝟙
dup-free (x ∷ xs) = ¬ (x ∈ xs) × dup-free xs

∈-++-left : {X : 𝓤 ̇ } {x : X} (xs ys : List X) → x ∈ xs → x ∈ (xs ++ ys)
∈-++-left []       ys ()
∈-++-left (y ∷ xs) ys (inl e) = inl e
∈-++-left (y ∷ xs) ys (inr m) = inr (∈-++-left xs ys m)

∈-++-right : {X : 𝓤 ̇ } {x : X} (xs ys : List X) → x ∈ ys → x ∈ (xs ++ ys)
∈-++-right []       ys m = m
∈-++-right (y ∷ xs) ys m = inr (∈-++-right xs ys m)

∈-++-split : {X : 𝓤 ̇ } {x : X} (xs ys : List X) → x ∈ (xs ++ ys)
           → (x ∈ xs) ∔ (x ∈ ys)
∈-++-split []       ys m       = inr m
∈-++-split (y ∷ xs) ys (inl e) = inl (inl e)
∈-++-split (y ∷ xs) ys (inr m) =
 cases (λ m' → inl (inr m')) inr (∈-++-split xs ys m)

∈-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x : X} (xs : List X) → x ∈ xs
      → f x ∈ map f xs
∈-map f []       ()
∈-map f (y ∷ xs) (inl e) = inl (ap f e)
∈-map f (y ∷ xs) (inr m) = inr (∈-map f xs m)

∈-map⁻¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {z : Y} (xs : List X)
        → z ∈ map f xs → Σ x ꞉ X , (x ∈ xs) × (f x ＝ z)
∈-map⁻¹ f []       ()
∈-map⁻¹ f (y ∷ xs) (inl e) = y , inl refl , (e ⁻¹)
∈-map⁻¹ f (y ∷ xs) (inr m) = pr₁ r , inr (pr₁ (pr₂ r)) , pr₂ (pr₂ r)
 where
  r = ∈-map⁻¹ f xs m

∈-concat-map
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → List Y) (xs : List X) {x : X} {y : Y}
             → x ∈ xs → y ∈ f x → y ∈ concat (map f xs)
∈-concat-map f []        ()      m
∈-concat-map f (x' ∷ xs) {x} {y} (inl e) m =
 ∈-++-left (f x') (concat (map f xs)) (transport (λ - → y ∈ f -) e m)
∈-concat-map f (x' ∷ xs) (inr m') m =
 ∈-++-right (f x') (concat (map f xs)) (∈-concat-map f xs m' m)

∈-concat-map⁻¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → List Y) (xs : List X) {y : Y}
               → y ∈ concat (map f xs) → Σ x ꞉ X , (x ∈ xs) × (y ∈ f x)
∈-concat-map⁻¹ f []       ()
∈-concat-map⁻¹ f (x ∷ xs) m = cases (λ m' → x , inl refl , m') γ
                                     (∈-++-split (f x) (concat (map f xs)) m)
 where
  γ : _ ∈ concat (map f xs) → Σ x' ꞉ _ , (x' ∈ (x ∷ xs)) × (_ ∈ f x')
  γ m' = pr₁ r , inr (pr₁ (pr₂ r)) , pr₂ (pr₂ r)
   where
    r = ∈-concat-map⁻¹ f xs m'

dup-free-++ : {X : 𝓤 ̇ } (xs ys : List X) → dup-free xs → dup-free ys
            → ((x : X) → x ∈ xs → ¬ (x ∈ ys)) → dup-free (xs ++ ys)
dup-free-++ []       ys _          dys disj = dys
dup-free-++ (x ∷ xs) ys (x∉ , dxs) dys disj =
 (λ m → cases x∉ (disj x (inl refl)) (∈-++-split xs ys m)) ,
 dup-free-++ xs ys dxs dys (λ y m → disj y (inr m))

dup-free-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
             → ((x x' : X) → f x ＝ f x' → x ＝ x')
             → (xs : List X) → dup-free xs → dup-free (map f xs)
dup-free-map f lc []       _          = ⋆
dup-free-map f lc (x ∷ xs) (x∉ , dxs) = γ , dup-free-map f lc xs dxs
 where
  γ : ¬ (f x ∈ map f xs)
  γ m = x∉ (transport (_∈ xs) (lc (pr₁ r) x (pr₂ (pr₂ r))) (pr₁ (pr₂ r)))
   where
    r = ∈-map⁻¹ f xs m

dup-free-concat-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → List Y) (xs : List X)
                    → dup-free xs
                    → ((x : X) → dup-free (f x))
                    → ((x x' : X) (y : Y) → y ∈ f x → y ∈ f x' → x ＝ x')
                    → dup-free (concat (map f xs))
dup-free-concat-map f []       _          df disj = ⋆
dup-free-concat-map f (x ∷ xs) (x∉ , dxs) df disj =
 dup-free-++ (f x) (concat (map f xs)) (df x)
  (dup-free-concat-map f xs dxs df disj) γ
 where
  γ : (y : _) → y ∈ f x → ¬ (y ∈ concat (map f xs))
  γ y m m' =
   x∉ (transport (_∈ xs) (disj (pr₁ r) x y (pr₂ (pr₂ r)) m) (pr₁ (pr₂ r)))
   where
    r = ∈-concat-map⁻¹ f xs m'

length-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (xs : List X)
           → length (map f xs) ＝ length xs
length-map f []       = refl
length-map f (x ∷ xs) = ap succ (length-map f xs)

\end{code}

Sums modulo 2.

\begin{code}

sum : {X : 𝓤 ̇ } → (X → 𝟚) → List X → 𝟚
sum w []       = ₀
sum w (x ∷ xs) = w x ⊕ sum w xs

sum-++ : {X : 𝓤 ̇ } (w : X → 𝟚) (xs ys : List X)
       → sum w (xs ++ ys) ＝ sum w xs ⊕ sum w ys
sum-++ w []       ys = refl
sum-++ w (x ∷ xs) ys =
 ap (w x ⊕_) (sum-++ w xs ys) ∙ ⊕-assoc {w x} {sum w xs} {sum w ys} ⁻¹

sum-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (w : Y → 𝟚) (f : X → Y) (xs : List X)
        → sum w (map f xs) ＝ sum (w ∘ f) xs
sum-map w f []       = refl
sum-map w f (x ∷ xs) = ap (w (f x) ⊕_) (sum-map w f xs)

sum-ext : {X : 𝓤 ̇ } (w w' : X → 𝟚) (xs : List X)
        → ((x : X) → x ∈ xs → w x ＝ w' x) → sum w xs ＝ sum w' xs
sum-ext w w' []       e = refl
sum-ext w w' (x ∷ xs) e =
 ap₂ _⊕_ (e x (inl refl)) (sum-ext w w' xs (λ y m → e y (inr m)))

sum-of-zeros : {X : 𝓤 ̇ } (w : X → 𝟚) (xs : List X)
             → ((x : X) → x ∈ xs → w x ＝ ₀) → sum w xs ＝ ₀
sum-of-zeros w []       e = refl
sum-of-zeros w (x ∷ xs) e =
 ap₂ _⊕_ (e x (inl refl)) (sum-of-zeros w xs (λ y m → e y (inr m)))

sum-⊕ : {X : 𝓤 ̇ } (w w' : X → 𝟚) (xs : List X)
      → sum (λ x → w x ⊕ w' x) xs ＝ sum w xs ⊕ sum w' xs
sum-⊕ w w' []       = refl
sum-⊕ w w' (x ∷ xs) =
 ap ((w x ⊕ w' x) ⊕_) (sum-⊕ w w' xs) ∙ γ (w x) (w' x) (sum w xs) (sum w' xs)
 where
  γ : (a b c d : 𝟚) → (a ⊕ b) ⊕ (c ⊕ d) ＝ (a ⊕ c) ⊕ (b ⊕ d)
  γ a b c d = ⊕-assoc {a} {b} {c ⊕ d} ∙ ap (a ⊕_) (xor-left-swap b c d)
              ∙ ⊕-assoc {a} {c} {b ⊕ d} ⁻¹

sum-is-one : {X : 𝓤 ̇ } (w : X → 𝟚) (xs : List X) → sum w xs ＝ ₁
           → Σ x ꞉ X , (x ∈ xs) × (w x ＝ ₁)
sum-is-one w []       e = 𝟘-elim (zero-is-not-one e)
sum-is-one w (x ∷ xs) e =
 cases (λ e' → x , inl refl , e') γ (xor-is-one (w x) (sum w xs) e)
 where
  γ : sum w xs ＝ ₁ → Σ y ꞉ _ , (y ∈ (x ∷ xs)) × (w y ＝ ₁)
  γ e' = pr₁ r , inr (pr₁ (pr₂ r)) , pr₂ (pr₂ r)
   where
    r = sum-is-one w xs e'

sum-concat-map
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (w : Y → 𝟚) (f : X → List Y) (xs : List X)
               → sum w (concat (map f xs)) ＝ sum (λ x → sum w (f x)) xs
sum-concat-map w f []       = refl
sum-concat-map w f (x ∷ xs) = sum-++ w (f x) (concat (map f xs))
                            ∙ ap (sum w (f x) ⊕_) (sum-concat-map w f xs)

\end{code}

A sum whose terms vanish except at one entry.

\begin{code}

sum-single : {X : 𝓤 ̇ } (w : X → 𝟚) (xs : List X) (a : X)
           → dup-free xs → a ∈ xs → ((x : X) → x ∈ xs → ¬ (x ＝ a) → w x ＝ ₀)
           → sum w xs ＝ w a
sum-single w []       a _          ()      h
sum-single w (x ∷ xs) a (x∉ , dxs) (inl e) h =
 ap₂ _⊕_ (ap w (e ⁻¹)) (sum-of-zeros w xs
   (λ y m → h y (inr m) (λ e' → x∉ (transport (_∈ xs) (e' ∙ e) m))))
 ∙ xor-right-unit (w a)
sum-single w (x ∷ xs) a (x∉ , dxs) (inr m) h =
 ap (_⊕ sum w xs) (h x (inl refl) (λ e → x∉ (transport (_∈ xs) (e ⁻¹) m)))
 ∙ sum-single w xs a dxs m (λ y m' → h y (inr m'))

\end{code}

Removing an element from a list over a type with decidable equality,
membership and inclusion as decidable propositions, the cancellation
lemma K0, the pigeonhole principle and the general door count of K2.

\begin{code}

remove-at : {X : 𝓤 ̇ } → ℕ → List X → List X
remove-at k        []       = []
remove-at 0        (x ∷ xs) = xs
remove-at (succ k) (x ∷ xs) = x ∷ remove-at k xs

length-remove-at : {X : 𝓤 ̇ } (k : ℕ) (xs : List X)
                 → k < length xs → succ (length (remove-at k xs)) ＝ length xs
length-remove-at k        []       l = 𝟘-elim l
length-remove-at 0        (x ∷ xs) l = refl
length-remove-at (succ k) (x ∷ xs) l = ap succ (length-remove-at k xs l)

range : ℕ → List ℕ
range 0        = []
range (succ m) = 0 ∷ map succ (range m)

range-member : (k m : ℕ) → k ∈ range m → k < m
range-member k 0        ()
range-member k (succ m) (inl e) = transport (_< succ m) (e ⁻¹) ⋆
range-member k (succ m) (inr n) =
 transport (_< succ m) (pr₂ (pr₂ r)) (range-member (pr₁ r) m (pr₁ (pr₂ r)))
 where
  r = ∈-map⁻¹ succ (range m) n

range-member⁻¹ : (k m : ℕ) → k < m → k ∈ range m
range-member⁻¹ 0        0        ()
range-member⁻¹ (succ k) 0        ()
range-member⁻¹ 0        (succ m) l = inl refl
range-member⁻¹ (succ k) (succ m) l =
 inr (∈-map succ (range m) (range-member⁻¹ k m l))

length-range : (m : ℕ) → length (range m) ＝ m
length-range 0        = refl
length-range (succ m) = ap succ (length-map succ (range m) ∙ length-range m)

range-dup-free : (m : ℕ) → dup-free (range m)
range-dup-free 0        = ⋆
range-dup-free (succ m) =
 γ , dup-free-map succ (λ x x' → succ-lc) (range m) (range-dup-free m)
 where
  γ : ¬ (0 ∈ map succ (range m))
  γ n = positive-not-zero (pr₁ r) (pr₂ (pr₂ r))
   where
    r = ∈-map⁻¹ succ (range m) n

module _ {X : 𝓤 ̇ } (d : is-discrete X) where

 remove-step : {x y : X} → is-decidable (x ＝ y) → List X → List X
 remove-step         (inl _) zs = zs
 remove-step {x} {y} (inr _) zs = x ∷ zs

 remove : X → List X → List X
 remove y []       = []
 remove y (x ∷ xs) = remove-step (d x y) (remove y xs)

 remove-length : (y : X) (xs : List X) → length (remove y xs) ≤ length xs
 remove-length y []       = ⋆
 remove-length y (x ∷ xs) = γ (d x y)
  where
   γ : (e : is-decidable (x ＝ y))
     → length (remove-step e (remove y xs)) ≤ succ (length xs)
   γ (inl _) = ≤-trans (length (remove y xs)) (length xs) (succ (length xs))
                (remove-length y xs) (≤-succ (length xs))
   γ (inr _) = remove-length y xs

 remove-length-strict : (y : X) (xs : List X) → y ∈ xs
                      → length (remove y xs) < length xs
 remove-length-strict y []       ()
 remove-length-strict y (x ∷ xs) m = γ (d x y) m
  where
   γ : (e : is-decidable (x ＝ y)) → y ∈ (x ∷ xs)
     → length (remove-step e (remove y xs)) < succ (length xs)
   γ (inl _) _        = remove-length y xs
   γ (inr u) (inl e)  = 𝟘-elim (u (e ⁻¹))
   γ (inr u) (inr m') = remove-length-strict y xs m'

 remove-member : (y z : X) (xs : List X) → z ∈ remove y xs
               → (z ∈ xs) × ¬ (z ＝ y)
 remove-member y z []       ()
 remove-member y z (x ∷ xs) = γ (d x y)
  where
   γ : (e : is-decidable (x ＝ y)) → z ∈ remove-step e (remove y xs)
     → (z ∈ (x ∷ xs)) × ¬ (z ＝ y)
   γ (inl _) m       =
    inr (pr₁ (remove-member y z xs m)) , pr₂ (remove-member y z xs m)
   γ (inr u) (inl e) = inl e , (λ e' → u (e ⁻¹ ∙ e'))
   γ (inr u) (inr m) =
    inr (pr₁ (remove-member y z xs m)) , pr₂ (remove-member y z xs m)

 remove-member⁻¹ : (y z : X) (xs : List X) → z ∈ xs → ¬ (z ＝ y)
                 → z ∈ remove y xs
 remove-member⁻¹ y z []       () ne
 remove-member⁻¹ y z (x ∷ xs) m ne = γ (d x y) m
  where
   γ : (e : is-decidable (x ＝ y)) → z ∈ (x ∷ xs)
     → z ∈ remove-step e (remove y xs)
   γ (inl e) (inl e') = 𝟘-elim (ne (e' ∙ e))
   γ (inl e) (inr m') = remove-member⁻¹ y z xs m' ne
   γ (inr u) (inl e') = inl e'
   γ (inr u) (inr m') = inr (remove-member⁻¹ y z xs m' ne)

 remove-dup-free : (y : X) (xs : List X) → dup-free xs → dup-free (remove y xs)
 remove-dup-free y []       _          = ⋆
 remove-dup-free y (x ∷ xs) (x∉ , dxs) = γ (d x y)
  where
   γ : (e : is-decidable (x ＝ y)) → dup-free (remove-step e (remove y xs))
   γ (inl _) = remove-dup-free y xs dxs
   γ (inr u) =
    (λ m → x∉ (pr₁ (remove-member y x xs m))) , remove-dup-free y xs dxs

 remove-absent : (y : X) (xs : List X) → ¬ (y ∈ xs) → remove y xs ＝ xs
 remove-absent y []       _ = refl
 remove-absent y (x ∷ xs) n = γ (d x y)
  where
   γ : (e : is-decidable (x ＝ y)) → remove-step e (remove y xs) ＝ x ∷ xs
   γ (inl e) = 𝟘-elim (n (inl (e ⁻¹)))
   γ (inr _) = ap (x ∷_) (remove-absent y xs (λ m → n (inr m)))

 remove-sum : (w : X → 𝟚) (y : X) (xs : List X)
            → dup-free xs → y ∈ xs → sum w xs ＝ w y ⊕ sum w (remove y xs)
 remove-sum w y []       _          ()
 remove-sum w y (x ∷ xs) (x∉ , dxs) m = γ (d x y) m
  where
   γ : (e : is-decidable (x ＝ y)) → y ∈ (x ∷ xs)
     → w x ⊕ sum w xs ＝ w y ⊕ sum w (remove-step e (remove y xs))
   γ (inl e) _        = ap (λ - → w - ⊕ sum w xs) e
                      ∙ ap (λ - → w y ⊕ sum w -)
                           (remove-absent y xs
                             (λ m' → x∉ (transport (_∈ xs) (e ⁻¹) m'))) ⁻¹
   γ (inr u) (inl e)  = 𝟘-elim (u (e ⁻¹))
   γ (inr u) (inr m') = ap (w x ⊕_) (remove-sum w y xs dxs m')
                      ∙ xor-left-swap (w x) (w y) (sum w (remove y xs))

 remove-length-exact : (y : X) (xs : List X)
                     → dup-free xs → y ∈ xs
                     → succ (length (remove y xs)) ＝ length xs
 remove-length-exact y []       _          ()
 remove-length-exact y (x ∷ xs) (x∉ , dxs) m = γ (d x y) m
  where
   γ : (e : is-decidable (x ＝ y)) → y ∈ (x ∷ xs)
     → succ (length (remove-step e (remove y xs))) ＝ succ (length xs)
   γ (inl e) _        = ap (λ - → succ (length -))
                           (remove-absent y xs
                             (λ m' → x∉ (transport (_∈ xs) (e ⁻¹) m')))
   γ (inr u) (inl e)  = 𝟘-elim (u (e ⁻¹))
   γ (inr u) (inr m') = ap succ (remove-length-exact y xs dxs m')

 ∈-decidable : (x : X) (xs : List X) → is-decidable (x ∈ xs)
 ∈-decidable x []       = inr 𝟘-elim
 ∈-decidable x (y ∷ ys) = +-preserves-decidability (d x y) (∈-decidable x ys)

 ⊆-decidable : (xs ys : List X) → is-decidable (xs ⊆ ys)
 ⊆-decidable []       ys = inl (λ z m → 𝟘-elim m)
 ⊆-decidable (x ∷ xs) ys = γ (∈-decidable x ys) (⊆-decidable xs ys)
  where
   γ : is-decidable (x ∈ ys) → is-decidable (xs ⊆ ys)
     → is-decidable ((x ∷ xs) ⊆ ys)
   γ (inl a) (inl b) =
    inl (λ z m → cases (λ e → transport (_∈ ys) (e ⁻¹) a) (b z) m)
   γ (inl a) (inr v) = inr (λ h → v (λ z m → h z (inr m)))
   γ (inr u) _       = inr (λ h → u (h x (inl refl)))

 outside : List X → List X → 𝓤 ̇
 outside xs S = Σ y ꞉ X , (y ∈ xs) × ¬ (y ∈ S)

 outside-decidable : (xs S : List X) → is-decidable (outside xs S)
 outside-decidable []       S = inr (λ o → 𝟘-elim (pr₁ (pr₂ o)))
 outside-decidable (x ∷ xs) S = γ (∈-decidable x S) (outside-decidable xs S)
  where
   γ : is-decidable (x ∈ S) → is-decidable (outside xs S)
     → is-decidable (outside (x ∷ xs) S)
   γ (inr u) _       = inl (x , inl refl , u)
   γ (inl a) (inl o) = inl (pr₁ o , inr (pr₁ (pr₂ o)) , pr₂ (pr₂ o))
   γ (inl a) (inr v) = inr δ
    where
     δ : ¬ outside (x ∷ xs) S
     δ (y , inl e , u) = u (transport (_∈ S) (e ⁻¹) a)
     δ (y , inr m , u) = v (y , m , u)

\end{code}

K0, the cancellation lemma. The induction is on the length of the
list; each step removes the head x and, if T x ≠ x, also T x.

\begin{code}

 module _ (T : X → X) (w : X → 𝟚) where

  Closed Involutive Invariant Free : List X → 𝓤 ̇
  Closed     xs = (x : X) → x ∈ xs → T x ∈ xs
  Involutive xs = (x : X) → x ∈ xs → T (T x) ＝ x
  Invariant  xs = (x : X) → x ∈ xs → w (T x) ＝ w x
  Free       xs = (x : X) → x ∈ xs → w x ＝ ₁ → ¬ (T x ＝ x)

  cancellation : (xs : List X)
               → dup-free xs → Closed xs → Involutive xs → Invariant xs
               → Free xs
               → sum w xs ＝ ₀
  cancellation = course-of-values-induction-on-length P step
   where
    P : List X → 𝓤 ̇
    P xs = dup-free xs → Closed xs → Involutive xs → Invariant xs → Free xs
           → sum w xs ＝ ₀

    step : (xs : List X) → ((ys : List X) → length ys < length xs → P ys) → P xs
    step []       IH _          cl inv inw fr = refl
    step (x ∷ ys) IH (x∉ , dys) cl inv inw fr = γ (d (T x) x)
     where
      γ : is-decidable (T x ＝ x) → sum w (x ∷ ys) ＝ ₀
      γ (inl fixed) = ap (_⊕ sum w ys) w-x-is-₀
                    ∙ IH ys (<-succ (length ys)) dys cl' (λ y m → inv y (inr m))
                         (λ y m → inw y (inr m)) (λ y m → fr y (inr m))
       where
        w-x-is-₀ : w x ＝ ₀
        w-x-is-₀ = different-from-₁-equal-₀ (λ e → fr x (inl refl) e fixed)

        cl' : Closed ys
        cl' y m = cases δ id (cl y (inr m))
         where
          δ : T y ＝ x → T y ∈ ys
          δ e =
           𝟘-elim (x∉ (transport (_∈ ys) (inv y (inr m) ⁻¹ ∙ ap T e ∙ fixed) m))

      γ (inr moved) = ap (w x ⊕_) (remove-sum w (T x) ys dys Tx∈ys)
                    ∙ ap (λ - → w x ⊕ (- ⊕ sum w zs)) (inw x (inl refl))
                    ∙ ap (λ - → w x ⊕ (w x ⊕ -)) rest
                    ∙ ap (w x ⊕_) (xor-right-unit (w x))
                    ∙ γ₀ (w x)
       where
        γ₀ : (b : 𝟚) → b ⊕ b ＝ ₀
        γ₀ ₀ = refl
        γ₀ ₁ = refl

        Tx∈ys : T x ∈ ys
        Tx∈ys = cases (λ e → 𝟘-elim (moved e)) id (cl x (inl refl))

        zs : List X
        zs = remove (T x) ys

        shorter : length zs < length (x ∷ ys)
        shorter = <-trans (length zs) (length ys) (succ (length ys))
                   (remove-length-strict (T x) ys Tx∈ys) (<-succ (length ys))

        cl' : Closed zs
        cl' z m = remove-member⁻¹ (T x) (T z) ys Tz∈ys Tz≠Tx
         where
          z∈ys : z ∈ ys
          z∈ys = pr₁ (remove-member (T x) z ys m)

          z≠Tx : ¬ (z ＝ T x)
          z≠Tx = pr₂ (remove-member (T x) z ys m)

          Tz∈ys : T z ∈ ys
          Tz∈ys = cases (λ e → 𝟘-elim (z≠Tx (inv z (inr z∈ys) ⁻¹ ∙ ap T e))) id
                   (cl z (inr z∈ys))

          Tz≠Tx : ¬ (T z ＝ T x)
          Tz≠Tx e = x∉ (transport (_∈ ys)
                         (inv z (inr z∈ys) ⁻¹ ∙ ap T e ∙ inv x (inl refl)) z∈ys)

        rest : sum w zs ＝ ₀
        rest = IH zs shorter (remove-dup-free (T x) ys dys) cl'
                (λ z m → inv z (inr (pr₁ (remove-member (T x) z ys m))))
                (λ z m → inw z (inr (pr₁ (remove-member (T x) z ys m))))
                (λ z m → fr z (inr (pr₁ (remove-member (T x) z ys m))))

\end{code}

The pigeonhole principle for lists.

\begin{code}

 pigeonhole : (S ys : List X) → dup-free S → S ⊆ ys → length S ≤ length ys
 pigeonhole []      ys _          _   = ⋆
 pigeonhole (s ∷ S) ys (s∉ , dS) sub =
  ≤-<-trans (length S) (length (remove s ys)) (length ys)
   (pigeonhole S (remove s ys) dS γ)
    (remove-length-strict s ys (sub s (inl refl)))
  where
   γ : S ⊆ remove s ys
   γ t m =
    remove-member⁻¹ s t ys (sub t (inr m)) (λ e → s∉ (transport (_∈ S) e m))

 too-short : (S ys : List X) → dup-free S → S ⊆ ys → length ys < length S → 𝟘
 too-short S ys dS sub l =
  not-less-than-itself (length S)
   (≤-<-trans (length S) (length ys) (length S) (pigeonhole S ys dS sub) l)

\end{code}

The general form of K2: the number of positions whose removal keeps
every element of S is odd exactly when every element of S occurs and
some entry is outside S.

\begin{code}

 sub-cons→ : (S Y : List X) (x : X) → S ⊆ (x ∷ Y) → remove x S ⊆ Y
 sub-cons→ S Y x h z m = cases (λ e → 𝟘-elim (pr₂ (remove-member x z S m) e)) id
                          (h z (pr₁ (remove-member x z S m)))

 sub-cons← : (S Y : List X) (x : X) → remove x S ⊆ Y → S ⊆ (x ∷ Y)
 sub-cons← S Y x h z m =
  cases inl (λ ne → inr (h z (remove-member⁻¹ x z S m ne))) (d z x)

 door-count : (xs S : List X) → dup-free S → length xs ＝ succ (length S)
            → sum (λ k → χ (⊆-decidable S (remove-at k xs))) (range (length xs))
            ＝ χ (×-preserves-decidability (⊆-decidable S xs)
                  (outside-decidable xs S))
 door-count []       S dS ()
 door-count (x ∷ xs) S dS e = split ∙ γ (∈-decidable x S)
  where
   L : ℕ
   L = length xs

   L-is : L ＝ length S
   L-is = succ-lc e

   f : ℕ → 𝟚
   f k = χ (⊆-decidable S (remove-at k (x ∷ xs)))

   g : ℕ → 𝟚
   g k = χ (⊆-decidable S (x ∷ remove-at k xs))

   split : sum f (range (succ L)) ＝ χ (⊆-decidable S xs) ⊕ sum g (range L)
   split = ap (f 0 ⊕_) (sum-map f succ (range L))

   dE : is-decidable (S ⊆ xs)
   dE = ⊆-decidable S xs

   dR : is-decidable ((S ⊆ (x ∷ xs)) × outside (x ∷ xs) S)
   dR = ×-preserves-decidability (⊆-decidable S (x ∷ xs))
         (outside-decidable (x ∷ xs) S)

   R : 𝟚
   R = χ dR

   γ : is-decidable (x ∈ S) → χ dE ⊕ sum g (range L) ＝ R
   γ (inr u) = ap (χ dE ⊕_) zeros ∙ xor-right-unit (χ dE) ∙ final
    where
     impossible : (k : ℕ) → k ∈ range L → ¬ (S ⊆ (x ∷ remove-at k xs))
     impossible k m h =
      too-short S (remove-at k xs) dS (λ z n → sub-cons-absent z n) short
      where
       sub-cons-absent : S ⊆ remove-at k xs
       sub-cons-absent z n =
        cases (λ e' → 𝟘-elim (u (transport (_∈ S) e' n))) id (h z n)

       short : length (remove-at k xs) < length S
       short = transport (succ (length (remove-at k xs)) ≤_)
                (length-remove-at k xs (range-member k L m) ∙ L-is)
                (≤-refl (succ (length (remove-at k xs))))

     zeros : sum g (range L) ＝ ₀
     zeros = sum-of-zeros g (range L)
              (λ k m →
                χ-no (⊆-decidable S (x ∷ remove-at k xs)) (impossible k m))

     final : χ dE ＝ R
     final = χ-↔ dE dR
              (λ h → (λ z m → inr (h z m)) , (x , inl refl , u))
              (λ p z m → cases (λ e' → 𝟘-elim (u (transport (_∈ S) e' m))) id
                          (pr₁ p z m))

   γ (inl a) =
    ap (χ dE ⊕_) (middle ∙ IH) ∙ δ (⊆-decidable S' xs) (∈-decidable x xs)
    where
     S' : List X
     S' = remove x S

     dS' : dup-free S'
     dS' = remove-dup-free x S dS

     dAB : is-decidable ((S' ⊆ xs) × outside xs S')
     dAB =
      ×-preserves-decidability (⊆-decidable S' xs) (outside-decidable xs S')

     AB : 𝟚
     AB = χ dAB

     IH : sum (λ k → χ (⊆-decidable S' (remove-at k xs))) (range L) ＝ AB
     IH = door-count xs S' dS' (L-is ∙ remove-length-exact x S dS a ⁻¹)

     middle : sum g (range L)
            ＝ sum (λ k → χ (⊆-decidable S' (remove-at k xs))) (range L)
     middle = sum-ext g _ (range L)
               (λ k _ → χ-↔ (⊆-decidable S (x ∷ remove-at k xs))
                         (⊆-decidable S' (remove-at k xs))
                          (sub-cons→ S (remove-at k xs) x)
                           (sub-cons← S (remove-at k xs) x))

     δ : is-decidable (S' ⊆ xs) → is-decidable (x ∈ xs) → χ dE ⊕ AB ＝ R
     δ (inr ¬A) _ =
      ap₂ _⊕_ (χ-no dE (λ h → ¬A (λ z m → h z (pr₁ (remove-member x z S m)))))
                            (χ-no dAB (λ p → ¬A (pr₁ p)))
                  ∙ (χ-no dR (λ p → ¬A (sub-cons→ S xs x (pr₁ p)))) ⁻¹
     δ (inl A) (inl x∈xs) =
      ap₂ _⊕_ (χ-yes dE S⊆xs) (χ-yes dAB (A , x , x∈xs , x∉S'))
                          ∙ (χ-no dR no-outside) ⁻¹
      where
       S⊆xs : S ⊆ xs
       S⊆xs z m = cases (λ e' → transport (_∈ xs) (e' ⁻¹) x∈xs)
                        (λ ne → A z (remove-member⁻¹ x z S m ne)) (d z x)

       x∉S' : ¬ (x ∈ S')
       x∉S' m = pr₂ (remove-member x x S m) refl

       no-outside : ¬ ((S ⊆ (x ∷ xs)) × outside (x ∷ xs) S)
       no-outside (_ , y , inl e' , u) = u (transport (_∈ S) (e' ⁻¹) a)
       no-outside (_ , y , inr m , u)  = too-short S (remove y xs) dS
                                          (λ z n →
                                            remove-member⁻¹ y z xs (S⊆xs z n)
                                                    (λ e' → u
                                                      (transport (_∈ S) e' n)))
                                          (transport (length (remove y xs) <_)
                                            L-is
                                            (remove-length-strict y xs m))
     δ (inl A) (inr x∉xs) =
      ap (_⊕ AB) (χ-no dE (λ h → x∉xs (h x a))) ∙ χ-↔ dAB dR there back
      where
       there : (S' ⊆ xs) × outside xs S' → (S ⊆ (x ∷ xs)) × outside (x ∷ xs) S
       there (A' , y , m , u) = sub-cons← S xs x A' ,
                                (y , inr m , (λ n → u (remove-member⁻¹ x y S n
                                                        (λ e' → x∉xs (transport
                                                          (_∈ xs) e' m)))))

       back : (S ⊆ (x ∷ xs)) × outside (x ∷ xs) S → (S' ⊆ xs) × outside xs S'
       back (h , y , inl e' , u) = 𝟘-elim (u (transport (_∈ S) (e' ⁻¹) a))
       back (h , y , inr m , u)  = sub-cons→ S xs x h ,
                                   (y , m ,
                                     (λ n → u (pr₁ (remove-member x y S n))))

\end{code}

Sums over the functions from Fin m to the entries of a list, and over
products of lists.

\begin{code}

cons : {A : 𝓤 ̇ } {m : ℕ} → A → (Fin m → A) → Fin (succ m) → A
cons a g (inl i) = g i
cons a g (inr ⋆) = a

functions : {A : 𝓤 ̇ } (m : ℕ) → List A → List (Fin m → A)
functions 0        as = (λ i → 𝟘-elim i) ∷ []
functions (succ m) as = concat (map (λ a → map (cons a) (functions m as)) as)

functions-member : {A : 𝓤 ̇ } (m : ℕ) (as : List A) (f : Fin m → A)
                 → f ∈ functions m as → (i : Fin m) → f i ∈ as
functions-member 0        as f h i = 𝟘-elim i
functions-member (succ m) as f h i = γ i
 where
  r = ∈-concat-map⁻¹ (λ a → map (cons a) (functions m as)) as h
  a = pr₁ r
  s = ∈-map⁻¹ (cons a) (functions m as) (pr₂ (pr₂ r))
  g = pr₁ s

  γ : (i : Fin (succ m)) → f i ∈ as
  γ (inl i) = transport (_∈ as) (ap (λ - → - (inl i)) (pr₂ (pr₂ s)))
               (functions-member m as g (pr₁ (pr₂ s)) i)
  γ (inr ⋆) =
   transport (_∈ as) (ap (λ - → - (inr ⋆)) (pr₂ (pr₂ s))) (pr₁ (pr₂ r))

functions-complete : {A : 𝓤 ̇ } → funext 𝓤₀ 𝓤
                   → (m : ℕ) (as : List A) (f : Fin m → A)
                   → ((i : Fin m) → f i ∈ as) → f ∈ functions m as
functions-complete fe 0        as f h = inl (dfunext fe (λ i → 𝟘-elim i))
functions-complete fe (succ m) as f h =
 ∈-concat-map (λ a → map (cons a) (functions m as)) as (h (inr ⋆))
  (transport (_∈ map (cons (f (inr ⋆))) (functions m as)) (dfunext fe η)
    (∈-map (cons (f (inr ⋆))) (functions m as)
      (functions-complete fe m as (λ i → f (inl i)) (λ i → h (inl i)))))
 where
  η : cons (f (inr ⋆)) (λ i → f (inl i)) ∼ f
  η (inl i) = refl
  η (inr ⋆) = refl

functions-dup-free : {A : 𝓤 ̇ } (m : ℕ) (as : List A) → dup-free as
                   → dup-free (functions m as)
functions-dup-free 0        as das = 𝟘-elim , ⋆
functions-dup-free (succ m) as das =
 dup-free-concat-map (λ a → map (cons a) (functions m as)) as das
  (λ a →
    dup-free-map (cons a) (λ g g' e → ap (λ h i → h (inl i)) e) (functions m as)
           (functions-dup-free m as das))
  disjoint
 where
  disjoint : (a a' : _) (f : _) → f ∈ map (cons a) (functions m as)
           → f ∈ map (cons a') (functions m as) → a ＝ a'
  disjoint a a' f n n' =
   ap (λ - → - (inr ⋆)) (pr₂ (pr₂ s)) ∙ ap (λ - → - (inr ⋆)) (pr₂ (pr₂ s')) ⁻¹
   where
    s  = ∈-map⁻¹ (cons a) (functions m as) n
    s' = ∈-map⁻¹ (cons a') (functions m as) n'

sum-functions-succ
 : {A : 𝓤 ̇ } (m : ℕ) (as : List A) (F : (Fin (succ m) → A) → 𝟚)
                   → sum F (functions (succ m) as)
                   ＝ sum (λ a → sum (λ g → F (cons a g)) (functions m as)) as
sum-functions-succ m as F =
 sum-concat-map F (λ a → map (cons a) (functions m as)) as
                          ∙ sum-ext _ _ as
                             (λ a _ → sum-map F (cons a) (functions m as))

product : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → List X → List Y → List (X × Y)
product xs ys = concat (map (λ x → map (x ,_) ys) xs)

sum-product : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (w : X × Y → 𝟚) (xs : List X) (ys : List Y)
            → sum w (product xs ys) ＝ sum (λ x → sum (λ y → w (x , y)) ys) xs
sum-product w xs ys = sum-concat-map w (λ x → map (x ,_) ys) xs
                    ∙ sum-ext _ _ xs (λ x _ → sum-map w (x ,_) ys)

product-member
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (xs : List X) (ys : List Y) {x : X} {y : Y}
               → x ∈ xs → y ∈ ys → (x , y) ∈ product xs ys
product-member xs ys m n =
 ∈-concat-map (λ x → map (x ,_) ys) xs m (∈-map (_ ,_) ys n)

product-member⁻¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (xs : List X) (ys : List Y) (z : X × Y)
                 → z ∈ product xs ys → (pr₁ z ∈ xs) × (pr₂ z ∈ ys)
product-member⁻¹ xs ys z m =
 transport (_∈ xs) (ap pr₁ (pr₂ (pr₂ s))) (pr₁ (pr₂ r)) ,
 transport (_∈ ys) (ap pr₂ (pr₂ (pr₂ s))) (pr₁ (pr₂ s))
 where
  r = ∈-concat-map⁻¹ (λ x → map (x ,_) ys) xs m
  s = ∈-map⁻¹ (pr₁ r ,_) ys (pr₂ (pr₂ r))

product-dup-free : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (xs : List X) (ys : List Y)
                 → dup-free xs → dup-free ys → dup-free (product xs ys)
product-dup-free xs ys dxs dys =
 dup-free-concat-map (λ x → map (x ,_) ys) xs dxs
  (λ x → dup-free-map (x ,_) (λ y y' e → ap pr₂ e) ys dys)
  (λ x x' z n n' → ap pr₁ (pr₂ (pr₂ (∈-map⁻¹ (x ,_) ys n)))
                   ∙ ap pr₁ (pr₂ (pr₂ (∈-map⁻¹ (x' ,_) ys n'))) ⁻¹)

\end{code}

Two reindexings for step K6: a sum over functions whose value at 𝟎 is
fixed, and a sum over functions to 0, …, m that avoid 0.

\begin{code}

sum-fixed-at-𝟎
 : {A : 𝓤 ̇ } (m : ℕ) (as : List A) (a : A) (F : (Fin (succ m) → A) → 𝟚)
               → dup-free as → a ∈ as
               → ((f : Fin (succ m) → A) → ¬ (f (inr ⋆) ＝ a) → F f ＝ ₀)
               → sum F (functions (succ m) as)
               ＝ sum (λ g → F (cons a g)) (functions m as)
sum-fixed-at-𝟎 m as a F das m-a h =
 sum-functions-succ m as F
 ∙ sum-single (λ a' → sum (λ g → F (cons a' g)) (functions m as)) as a das m-a
    (λ a' _ ne → sum-of-zeros _ (functions m as) (λ g _ → h (cons a' g) ne))

sum-avoiding-zero : funext 𝓤₀ 𝓤₀ → (m j : ℕ) (G : (Fin j → ℕ) → 𝟚)
                  → ((f : Fin j → ℕ) (i : Fin j) → f i ＝ 0 → G f ＝ ₀)
                  → sum G (functions j (range (succ m)))
                  ＝ sum (λ g → G (λ i → succ (g i))) (functions j (range m))
sum-avoiding-zero fe m 0        G h =
 ap (λ - → G - ⊕ ₀) (dfunext fe (λ i → 𝟘-elim i))
sum-avoiding-zero fe m (succ j) G h =
 sum-functions-succ j (range (succ m)) G
 ∙ ap (_⊕ sum (λ a → sum (λ g → G (cons a g)) (functions j (range (succ m))))
        (map succ (range m)))
      (sum-of-zeros _ (functions j (range (succ m)))
        (λ g _ → h (cons 0 g) (inr ⋆) refl))
 ∙ sum-map (λ a → sum (λ g → G (cons a g)) (functions j (range (succ m)))) succ
    (range m)
 ∙ sum-ext _ _ (range m) (λ a _ → IH a ∙ sum-ext _ _ (functions j (range m))
                                   (λ g _ → ap G (dfunext fe (shift a g))))
 ∙ sum-functions-succ j (range m) (λ g → G (λ i → succ (g i))) ⁻¹
 where
  IH : (a : ℕ) → sum (λ g → G (cons (succ a) g)) (functions j (range (succ m)))
               ＝ sum (λ g → G (cons (succ a) (λ i → succ (g i))))
                  (functions j (range m))
  IH a = sum-avoiding-zero fe m j (λ g → G (cons (succ a) g))
          (λ g i e → h (cons (succ a) g) (inl i) e)

  shift : (a : ℕ) (g : Fin j → ℕ)
        → cons (succ a) (λ i → succ (g i)) ∼ (λ i → succ (cons a g i))
  shift a g (inl i) = refl
  shift a g (inr ⋆) = refl

\end{code}

Decidable equality of functions from Fin m to a type with decidable
equality, by function extensionality, and of pairs.

\begin{code}

Fin-functions-are-discrete : {A : 𝓤 ̇ } → funext 𝓤₀ 𝓤 → is-discrete A
                           → (m : ℕ) → is-discrete (Fin m → A)
Fin-functions-are-discrete fe dA 0        f g =
 inl (dfunext fe (λ i → 𝟘-elim i))
Fin-functions-are-discrete fe dA (succ m) f g =
 γ (dA (f (inr ⋆)) (g (inr ⋆)))
  (Fin-functions-are-discrete fe dA m (λ i → f (inl i)) (λ i → g (inl i)))
 where
  γ : is-decidable (f (inr ⋆) ＝ g (inr ⋆))
    → is-decidable ((λ i → f (inl i)) ＝ (λ i → g (inl i)))
    → is-decidable (f ＝ g)
  γ (inl p) (inl q) = inl (dfunext fe δ)
   where
    δ : f ∼ g
    δ (inl i) = ap (λ - → - i) q
    δ (inr ⋆) = p
  γ (inl p) (inr v) = inr (λ r → v (ap (λ h i → h (inl i)) r))
  γ (inr u) _       = inr (λ r → u (ap (λ h → h (inr ⋆)) r))

pairs-are-discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → is-discrete X → is-discrete Y
                   → is-discrete (X × Y)
pairs-are-discrete dX dY (x , y) (x' , y') = γ (dX x x') (dY y y')
 where
  γ : is-decidable (x ＝ x') → is-decidable (y ＝ y')
    → is-decidable ((x , y) ＝ (x' , y'))
  γ (inl p) (inl q) = inl (ap₂ _,_ p q)
  γ (inl p) (inr v) = inr (λ r → v (ap pr₂ r))
  γ (inr u) _       = inr (λ r → u (ap pr₁ r))

\end{code}
