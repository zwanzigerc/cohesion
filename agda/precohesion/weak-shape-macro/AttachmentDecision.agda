{-# OPTIONS --cohesion --without-K --flat-split #-}

-- SET-SOURCE STAGES I3 and I4: three maps out of the shape of the
-- attachment, and the decision of equality up to P from a crisp section of
-- points-to-pieces and a crisp contraction of L. Opus, 14 November 2026;
-- opus-closed-limits-01 (delta 07), implementing FABLE-PLAN-SET-SOURCE-01
-- §7.3–7.4 (CLOSED-INTERVAL-DIRECT-EXTRACTION-01 §1–2) with the corrections
-- of SET-SOURCE-PLAN-ASTRA-RELEASE-01 (label at bottom/truth via the
-- endpoints; separate h false / h true; the same section on both
-- endpoints, the first representative a parameter of the second).
--
-- Generic in its data (plan §2; the kernel supplies its own instances):
-- crisp levels j = lsuc i, k = lsuc j; fe-j, pe-j, fe-k; the truncation Tk
-- at k; a truncation Tj and the support P at j; the closed carrier C : Set k
-- with C-set, its points bottom, truth-point and c3 : bottom ≡ truth-point
-- → P; a closed discrete SET G of level j; the attachment of the diagonal of
-- G given ABSTRACTLY by its carrier U, endpoints end (with end false/true
-- equal to the sharp units of bottom/truth-point), generators present,
-- attaching path, the I1 extension with its two laws and the I2 boxed cover
-- (the kernel client supplies Fable's Att data and AttachmentFacts); the
-- choices sC on ♯ C and sU on U.
--
--   I3a  π : S → Raise k (G × G) with π-vertex, π-middle   (S = ʃ sU)
--   I3b  kk-to-q : k false b ≡ k true b → q b              (χ of the diagonal)
--        q-to-kk : IsContr (ʃ sC) → q b → k false b ≡ k true b
--   I3c  d : ♭ U → C, h : (@♭ t : Bool) → G × G → ♭ U, d-h, θ-h,
--        hh-to-P : h false b ≡ h true b → P          (C4 for ♯ C, then C3)
--   I4   decide : (@♭ σ : PointsSection sU) (@♭ ct : IsContr (ʃ sC))
--             → (x y : G) → ∥ (x ≡ y) ⊎ ((x ≡ y) → P) ∥_j
-- The three cocones are the supplied I1 extensions into sets of level k. Nothing is postulated; no shape is formed.
module AttachmentDecision where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Foundations
open import NativeSharp
  using (♯; sharp-unit; sharp-extract; flat-sharp-counit; box-crisp-path)
open import CaptureContext using (Raise; raise; lower)
open import ShapeElim using (module SigmaDiscrete; raise-set; raise-discrete)
open import GlobalChoice using (×-set)
open import SmallPropositions using (PropExt; subtype-path)
open import GlobalPrecohesion
  using (ShapeData; ʃ; ʃ-set; ʃ-discrete; η; rec; rec-η; points-to-pieces;
         discrete-elim)
open import GlobalPropositions using (FunExt₂)
open import TruncationDiscrete using (_⊎_; inl; inr)
open import OrdinaryTruncation using (PropTruncation)
open import SmallQuotient using (Quotients; Eliminates)
open import BaseClassifier using (O; O-discrete; top)
open import BaseClassifierLaws using (module Laws)
open import MonoClassifier using (module Classification)
open import SharpSet using (sharp-is-set)
open import PointsPieces using (PointsSection)

module Decide {@♭ i : Level}
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) (@♭ pe-j : PropExt (lsuc i))
  (@♭ fe-k : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i)))
  (@♭ Tk : PropTruncation (lsuc (lsuc i)))
  (@♭ Tj : PropTruncation (lsuc i)) (@♭ P : Set (lsuc i))
  (@♭ C : Set (lsuc (lsuc i))) (@♭ C-set : IsSet C)
  (@♭ bottom truth-point : C) (@♭ c3 : bottom ≡ truth-point → P)
  (@♭ G : Set (lsuc i)) (@♭ dG : Discrete G) (@♭ G-set : IsSet G)
  -- the attachment, ABSTRACTLY: carrier, generators, attaching path, the
  -- two-generator extension into sets of level k with its two laws, and
  -- the boxed cover (I1, I2). The kernel passes its own Att data and the
  -- AttachmentFacts operations; no attachment type is restated here, so no
  -- two copies of Attachment are compared (§13.1).
  (@♭ U : Set (lsuc (lsuc i)))
  (@♭ end : Bool → ♯ C)
  (@♭ end-false : end false ≡ sharp-unit bottom)
  (@♭ end-true : end true ≡ sharp-unit truth-point)
  (@♭ present : ((G × G) × Bool) ⊎ (G × ♯ C) → U)
  (@♭ attach : (a : G) (t : Bool)
             → present (inl ((a , a) , t)) ≡ present (inr (a , end t)))
  (@♭ extend : {Y : Set (lsuc (lsuc i))} → IsSet Y
             → (fA : (G × G) × Bool → Y) (fD : G × ♯ C → Y)
             → ((a : G) (t : Bool) → fA ((a , a) , t) ≡ fD (a , end t))
             → U → Y)
  (@♭ extend-vertex : {Y : Set (lsuc (lsuc i))} (Y-set : IsSet Y)
             → (fA : (G × G) × Bool → Y) (fD : G × ♯ C → Y)
             → (ag : (a : G) (t : Bool) → fA ((a , a) , t) ≡ fD (a , end t))
             → (t : Bool) (b : G × G)
             → extend Y-set fA fD ag (present (inl (b , t))) ≡ fA (b , t))
  (@♭ extend-middle : {Y : Set (lsuc (lsuc i))} (Y-set : IsSet Y)
             → (fA : (G × G) × Bool → Y) (fD : G × ♯ C → Y)
             → (ag : (a : G) (t : Bool) → fA ((a , a) , t) ≡ fD (a , end t))
             → (a : G) (z : ♯ C)
             → extend Y-set fA fD ag (present (inr (a , z))) ≡ fD (a , z))
  (@♭ boxed-cover : (v : ♭ U)
             → PropTruncation.∥_∥ Tk (Fiber (flat-map present) v))
  (@♭ sC : ShapeData (♯ C))
  (@♭ sU : ShapeData U) where

  vertex : Bool → G × G → U
  vertex t b = present (inl (b , t))

  middle : G → ♯ C → U
  middle a z = present (inr (a , z))

  S : Set (lsuc (lsuc i))
  S = ʃ sU

  θ : ♭ U → S
  θ = points-to-pieces sU

  k : Bool → G × G → S
  k t b = η sU (vertex t b)

  GG-discrete : Discrete (G × G)
  GG-discrete = SigmaDiscrete.discrete dG (λ _ → dG)

  GG-set : IsSet (G × G)
  GG-set = ×-set G-set G-set

  q : G × G → Set (lsuc i)
  q b = fst b ≡ snd b

  ----------------------------------------------------------------------
  -- I3a. The projection to the base.

  private
    π-fA : (G × G) × Bool → Raise (lsuc (lsuc i)) (G × G)
    π-fA w = raise (fst w)
    π-fD : G × ♯ C → Raise (lsuc (lsuc i)) (G × G)
    π-fD w = raise (fst w , fst w)
    π-ag : (a : G) (t : Bool) → π-fA ((a , a) , t) ≡ π-fD (a , end t)
    π-ag a t = refl

  πU : U → Raise (lsuc (lsuc i)) (G × G)
  πU = extend (raise-set GG-set) π-fA π-fD π-ag

  π : S → Raise (lsuc (lsuc i)) (G × G)
  π = rec sU (Raise (lsuc (lsuc i)) (G × G)) (raise-set GG-set)
    (raise-discrete GG-discrete) πU

  π-vertex : (t : Bool) (b : G × G) → π (k t b) ≡ raise b
  π-vertex t b = rec-η sU _ (raise-set GG-set) (raise-discrete GG-discrete)
    πU (vertex t b) ∙ extend-vertex (raise-set GG-set) π-fA π-fD π-ag t b

  π-middle : (a : G) (z : ♯ C) → π (η sU (middle a z)) ≡ raise (a , a)
  π-middle a z = rec-η sU _ (raise-set GG-set) (raise-discrete GG-discrete)
    πU (middle a z) ∙ extend-middle (raise-set GG-set) π-fA π-fD π-ag a z

  ----------------------------------------------------------------------
  -- I3b. The two vertices over b agree exactly when q b (given ct).

  diag : G → G × G
  diag x = x , x

  diag-mono : (w : G × G) → IsProp (Fiber diag w)
  diag-mono w (x , r) (y , s) =
    subtype-path (λ z → GG-set (diag z) w) (ap fst r ∙ sym (ap fst s))

  module Ch = Classification fe-j pe-j GG-discrete dG diag diag-mono

  O-set : IsSet (O (lsuc i))
  O-set = Laws.O-is-set fe-j pe-j

  private
    vertex-code : (G × G) × Bool → O (lsuc i)
    vertex-code (b , false) = Ch.χ b
    vertex-code (b , true) = top

    vertex-agree : (a : G) (t : Bool)
                 → vertex-code ((a , a) , t) ≡ top
    vertex-agree a false = Ch.truth-square a
    vertex-agree a true = refl

  κU : U → O (lsuc i)
  κU = extend O-set vertex-code (λ _ → top) vertex-agree

  ρ : S → O (lsuc i)
  ρ = rec sU (O (lsuc i)) O-set O-discrete κU

  ρ-vertex : (t : Bool) (b : G × G) → ρ (k t b) ≡ vertex-code (b , t)
  ρ-vertex t b = rec-η sU _ O-set O-discrete κU (vertex t b)
    ∙ extend-vertex O-set vertex-code (λ _ → top) vertex-agree t b

  kk-to-q : (b : G × G) → k false b ≡ k true b → q b
  kk-to-q b e = sym (ap fst (snd fib)) ∙ ap snd (snd fib)
    where
    χ-top : Ch.χ b ≡ top
    χ-top = sym (ρ-vertex false b) ∙ ap ρ e ∙ ρ-vertex true b

    fib : Fiber diag b
    fib = Ch.to-fibre b (Laws.truth-out fe-j pe-j (Ch.χ b) χ-top)

  module WithContraction (ct : IsContr (ʃ sC)) where

    private
      contr-path : (x y : ʃ sC) → x ≡ y
      contr-path x y = sym (snd ct x) ∙ snd ct y

    at-diag : (@♭ a : G) → k false (a , a) ≡ k true (a , a)
    at-diag a =
      ap (η sU) (attach a false)
      ∙ sym (Ma-η (end false))
      ∙ ap Ma (contr-path _ _)
      ∙ Ma-η (end true)
      ∙ sym (ap (η sU) (attach a true))
      where
      Ma : ʃ sC → S
      Ma = rec sC S (ʃ-set sU) (ʃ-discrete sU) (λ z → η sU (middle a z))

      Ma-η : (z : ♯ C) → Ma (η sC z) ≡ η sU (middle a z)
      Ma-η = rec-η sC S (ʃ-set sU) (ʃ-discrete sU) (λ z → η sU (middle a z))

    all-diag : (a : G) → k false (a , a) ≡ k true (a , a)
    all-diag = discrete-elim dG (λ a → k false (a , a) ≡ k true (a , a)) at-diag

    q-to-kk : (b : G × G) → q b → k false b ≡ k true b
    q-to-kk (x , y) e = helper e
      where
      helper : {y : G} → x ≡ y → k false (x , y) ≡ k true (x , y)
      helper refl = all-diag x

  ----------------------------------------------------------------------
  -- I3c. The colour of a crisp generator, into the SET ♯ C (C4).

  private
    λ-fA : (G × G) × Bool → ♯ C
    λ-fA w = end (snd w)
    λ-fD : G × ♯ C → ♯ C
    λ-fD w = snd w
    λ-ag : (a : G) (t : Bool) → λ-fA ((a , a) , t) ≡ λ-fD (a , end t)
    λ-ag a t = refl

  λU : U → ♯ C
  λU = extend (sharp-is-set fe-k C-set) λ-fA λ-fD λ-ag

  d : ♭ U → C
  d (box x) = sharp-extract (λU x)

  label : (@♭ t : Bool) → C
  label t = sharp-extract (end t)

  h : (@♭ t : Bool) → G × G → ♭ U
  h t b = flat-map (vertex t) (inverse GG-discrete b)

  d-h : (@♭ t : Bool) (b : G × G) → d (h t b) ≡ label t
  d-h t b = helper (inverse GG-discrete b)
    where
    helper : (w : ♭ (G × G)) → d (flat-map (vertex t) w) ≡ label t
    helper (box b′) = ap flat-sharp-counit
      (box-crisp-path (extend-vertex (sharp-is-set fe-k C-set) λ-fA λ-fD λ-ag t b′))

  θ-h : (@♭ t : Bool) (b : G × G) → θ (h t b) ≡ k t b
  θ-h t b = ap (η sU)
    (flat-map-counit (vertex t) (inverse GG-discrete b)
     ∙ ap (vertex t) (section GG-discrete b))

  h-crisp : (@♭ t : Bool) (@♭ b : G × G) → h t b ≡ box (vertex t b)
  h-crisp t b = ap (flat-map (vertex t)) (retraction GG-discrete (box b))

  label-false : label false ≡ bottom
  label-false = ap flat-sharp-counit (box-crisp-path end-false)

  label-true : label true ≡ truth-point
  label-true = ap flat-sharp-counit (box-crisp-path end-true)

  hh-to-P : (b : G × G) → h false b ≡ h true b → P
  hh-to-P b e = c3 (sym label-false ∙ sym (d-h false b) ∙ ap d e ∙ d-h true b ∙ label-true)

  ----------------------------------------------------------------------
  -- I4. The decision.

  open PropTruncation Tk using () renaming (∥_∥ to ∥_∥k; ∥-rec to ∥-rec-k)
  open PropTruncation Tj using () renaming (∥_∥ to ∥_∥j; ∣_∣ to ∣_∣j; squash to squash-j)

  module WithSection (@♭ σ : PointsSection sU) (@♭ ct : IsContr (ʃ sC)) where

    s : S → ♭ U
    s = fst σ

    law : (z : S) → θ (s z) ≡ z
    law = snd σ

    open WithContraction ct using (q-to-kk)

    -- What one boxed representative of s (k t b) says: a middle point
    -- (q b), or a crisp vertex of colour false or true over b. (A sum, not
    -- a data type: the constructor types mention the crisp section.)
    Rep : (b : G × G) (t : Bool) → Set (lsuc (lsuc i))
    Rep b t = q b ⊎ ((s (k t b) ≡ h false b) ⊎ (s (k t b) ≡ h true b))

    mid : {b : G × G} {t : Bool} → q b → Rep b t
    mid = inl

    vF : {b : G × G} {t : Bool} → s (k t b) ≡ h false b → Rep b t
    vF e = inr (inl e)

    vT : {b : G × G} {t : Bool} → s (k t b) ≡ h true b → Rep b t
    vT e = inr (inr e)

    -- A crisp vertex representative lies over b (by π); so s (k t b) is h.
    to-h : (b : G × G) (t : Bool) (@♭ t′ : Bool) (@♭ b′ : G × G)
         → box (vertex t′ b′) ≡ s (k t b) → s (k t b) ≡ h t′ b
    to-h b t t′ b′ e = sym e ∙ sym (h-crisp t′ b′) ∙ ap (h t′) over-b
      where
      units : k t′ b′ ≡ k t b
      units = ap θ e ∙ law (k t b)

      over-b : b′ ≡ b
      over-b = ap lower (sym (π-vertex t′ b′) ∙ ap π units ∙ π-vertex t b)

    classify : (b : G × G) (t : Bool)
             → Fiber (flat-map present) (s (k t b)) → Rep b t
    classify b t (box (inr (a , z)) , e) = mid (sym (ap fst over) ∙ ap snd over)
      where
      units : η sU (middle a z) ≡ k t b
      units = ap θ e ∙ law (k t b)

      over : diag a ≡ b
      over = ap lower (sym (π-middle a z) ∙ ap π units ∙ π-vertex t b)
    classify b t (box (inl (b′ , false)) , e) = vF (to-h b t false b′ e)
    classify b t (box (inl (b′ , true)) , e) = vT (to-h b t true b′ e)

    Answer : G × G → Set (lsuc i)
    Answer b = ∥ q b ⊎ (q b → P) ∥j

    combine : (b : G × G) → Rep b false → Rep b true → Answer b
    combine b (inl e) _ = ∣ inl e ∣j
    combine b (inr (inr ef)) _ =
      ∣ inl (kk-to-q b (sym (law (k false b)) ∙ ap θ ef ∙ θ-h true b)) ∣j
    combine b (inr (inl _)) (inl e) = ∣ inl e ∣j
    combine b (inr (inl _)) (inr (inl et)) =
      ∣ inl (kk-to-q b (sym (sym (law (k true b)) ∙ ap θ et ∙ θ-h false b))) ∣j
    combine b (inr (inl ef)) (inr (inr et)) =
      ∣ inr (λ e → hh-to-P b (sym ef ∙ ap s (q-to-kk b e) ∙ et)) ∣j

    private
      raised-prop : (b : G × G) → IsProp (Raise (lsuc (lsuc i)) (Answer b))
      raised-prop b (raise x) (raise y) = ap raise (squash-j x y)

    decide : (x y : G) → ∥ (x ≡ y) ⊎ ((x ≡ y) → P) ∥j
    decide x y = lower (∥-rec-k (raised-prop b)
      (λ rf → ∥-rec-k (raised-prop b)
        (λ rt → raise (combine b (classify b false rf) (classify b true rt)))
        (boxed-cover (s (k true b))))
      (boxed-cover (s (k false b))))
      where
      b : G × G
      b = x , y

  decision : (@♭ σ : PointsSection sU) (@♭ ct : IsContr (ʃ sC))
           → (x y : G) → ∥ (x ≡ y) ⊎ ((x ≡ y) → P) ∥j
  decision σ ct = WithSection.decide σ ct
