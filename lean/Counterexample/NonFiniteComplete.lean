import Counterexample.IndexCategories
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Prime.Basic

/-! # The indexing category does not have all finite limits

The self-pullback of sign would have ten homomorphisms out of `C₂`.
Every object in the indexing category has a power of two such homomorphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Counterexample

abbrev Involutions (G : Type*) [Group G] := {x : G // x * x = 1}

def homOfInvolution {G : Type*} [Group G] (x : Involutions G) : C2 →* G where
  toFun u := if u = 1 then 1 else x.val
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp [x.property]

def c2HomEquivInvolutions (G : Type*) [Group G] : (C2 →* G) ≃ Involutions G where
  toFun f := ⟨f (-1), by rw [← map_mul]; norm_num⟩
  invFun := homOfInvolution
  left_inv f := by
    ext u
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp [homOfInvolution]
  right_inv x := by ext; simp [homOfInvolution]

def involutionsProd (G H : Type*) [Group G] [Group H] :
    Involutions (G × H) ≃ Involutions G × Involutions H where
  toFun x := (⟨x.val.1, congrArg Prod.fst x.property⟩,
    ⟨x.val.2, congrArg Prod.snd x.property⟩)
  invFun x := ⟨(x.1.val, x.2.val), Prod.ext x.1.property x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem involutions_ab_card (A : AbelianWord) :
    ∃ n : ℕ, Nat.card (Involutions A.Carrier) = 2 ^ n := by
  induction A with
  | unit => exact ⟨0, by rw [Nat.card_eq_fintype_card]; decide⟩
  | c2 => exact ⟨1, by rw [Nat.card_eq_fintype_card]; decide⟩
  | c3 => exact ⟨0, by rw [Nat.card_eq_fintype_card]; decide⟩
  | prod A B ihA ihB =>
    obtain ⟨m, hm⟩ := ihA
    obtain ⟨n, hn⟩ := ihB
    refine ⟨m + n, ?_⟩
    rw [Nat.card_congr (involutionsProd A.Carrier B.Carrier), Nat.card_prod,
      hm, hn, pow_add]

theorem involutions_group_card (G : GroupWord) :
    ∃ n : ℕ, Nat.card (Involutions G.Carrier) = 2 ^ n := by
  induction G with
  | s3 => exact ⟨2, by rw [Nat.card_eq_fintype_card]; decide⟩
  | ab A => exact involutions_ab_card A
  | prod G H ihG ihH =>
    obtain ⟨m, hm⟩ := ihG
    obtain ⟨n, hn⟩ := ihH
    refine ⟨m + n, ?_⟩
    rw [Nat.card_congr (involutionsProd G.Carrier H.Carrier), Nat.card_prod,
      hm, hn, pow_add]

abbrev CompatibleInvolutions :=
  {p : Involutions S3 × Involutions S3 //
    Equiv.Perm.sign p.1.val = Equiv.Perm.sign p.2.val}

theorem compatibleInvolutions_card : Nat.card CompatibleInvolutions = 10 := by
  rw [Nat.card_eq_fintype_card]
  decide

def compatiblePair {D : GroupWord} {p q : D ⟶ GroupWord.s3}
    (h : p ≫ signMorphism = q ≫ signMorphism)
    (f : C2 →* D.Carrier) : CompatibleInvolutions :=
  ⟨((c2HomEquivInvolutions S3) (p.comp f),
      (c2HomEquivInvolutions S3) (q.comp f)),
    congrArg (fun k => k (f (-1))) h⟩

theorem compatiblePair_bijective {D : GroupWord} {p q : D ⟶ GroupWord.s3}
    (h : IsPullback p q signMorphism signMorphism) :
    Function.Bijective (compatiblePair h.w) := by
  constructor
  · intro f g hfg
    apply h.hom_ext (W := GroupWord.ab .c2) (k := f) (l := g)
    · apply (c2HomEquivInvolutions S3).injective
      exact congrArg (fun z : CompatibleInvolutions => z.val.1) hfg
    · apply (c2HomEquivInvolutions S3).injective
      exact congrArg (fun z : CompatibleInvolutions => z.val.2) hfg
  · intro z
    let f : GroupWord.ab .c2 ⟶ GroupWord.s3 := homOfInvolution z.val.1
    let g : GroupWord.ab .c2 ⟶ GroupWord.s3 := homOfInvolution z.val.2
    have hfg : f ≫ signMorphism = g ≫ signMorphism := by
      apply (c2HomEquivInvolutions C2).injective
      apply Subtype.ext
      change Equiv.Perm.sign (homOfInvolution z.val.1 (-1)) =
        Equiv.Perm.sign (homOfInvolution z.val.2 (-1))
      simpa [homOfInvolution] using z.property
    refine ⟨h.lift f g hfg, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change (c2HomEquivInvolutions S3) ((h.lift f g hfg) ≫ p) = z.val.1
      rw [h.lift_fst]
      exact (c2HomEquivInvolutions S3).apply_symm_apply z.val.1
    · change (c2HomEquivInvolutions S3) ((h.lift f g hfg) ≫ q) = z.val.2
      rw [h.lift_snd]
      exact (c2HomEquivInvolutions S3).apply_symm_apply z.val.2

theorem pow_two_ne_ten (n : ℕ) : 2 ^ n ≠ (10 : ℕ) := by
  intro h
  have hd : 5 ∣ 2 ^ n := by rw [h]; decide
  have hf : 5 ∣ (2 : ℕ) := (by decide : Nat.Prime 5).dvd_of_dvd_pow hd
  norm_num at hf

/-- The pullback of sign along itself has no representative in the indexing category. -/
theorem no_sign_self_pullback (D : GroupWord) (p q : D ⟶ GroupWord.s3) :
    ¬ IsPullback p q signMorphism signMorphism := by
  intro h
  have hc : Nat.card (C2 →* D.Carrier) = 10 :=
    (Nat.card_congr (Equiv.ofBijective _ (compatiblePair_bijective h))).trans
      compatibleInvolutions_card
  rw [Nat.card_congr (c2HomEquivInvolutions D.Carrier)] at hc
  obtain ⟨n, hn⟩ := involutions_group_card D
  exact pow_two_ne_ten n (hn.symm.trans hc)

theorem indexing_category_not_finitely_complete : ¬ HasFiniteLimits GroupWord := by
  intro h
  let := h
  exact no_sign_self_pullback (pullback signMorphism signMorphism)
    (pullback.fst signMorphism signMorphism) (pullback.snd signMorphism signMorphism)
    (IsPullback.of_hasPullback signMorphism signMorphism)

end Counterexample
