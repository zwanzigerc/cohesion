import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.PUnit
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # The finite groups in the counterexample

This file uses integer units for the cyclic group of order two and the
alternating group on three letters for the cyclic group of order three.
All claims are proved in Lean's kernel; finite checks use `decide`.
-/

namespace Counterexample

open scoped commutatorElement

abbrev S3 := Equiv.Perm (Fin 3)
abbrev C2 := ℤˣ
abbrev C3 := alternatingGroup (Fin 3)

@[simp] theorem card_S3 : Fintype.card S3 = 6 := by decide
@[simp] theorem card_C2 : Fintype.card C2 = 2 := by decide
@[simp] theorem card_C3 : Fintype.card C3 = 3 := by decide

instance : CommGroup C3 := by
  letI := alternatingGroup.isMulCommutative_of_card_le_three
    (α := Fin 3) (by simp)
  exact { (inferInstance : Group C3) with mul_comm := mul_comm' }

/-- The group `C₃` has exponent three. -/
theorem c3_cube (x : C3) : x ^ 3 = 1 := by
  exact (by decide : ∀ y : C3, y ^ 3 = 1) x

/-- Every homomorphism `C₃ → C₂` is trivial. -/
theorem hom_c3_c2_apply (f : C3 →* C2) (x : C3) : f x = 1 := by
  have h : f x ^ 3 = 1 := by rw [← map_pow, c3_cube, map_one]
  rcases Int.units_eq_one_or (f x) with hf | hf
  · exact hf
  · rw [hf] at h
    have hInt := congrArg (fun u : C2 => (u : ℤ)) h
    norm_num at hInt

instance : Subsingleton (C3 →* C2) :=
  ⟨fun f g => MonoidHom.ext fun x =>
    (hom_c3_c2_apply f x).trans (hom_c3_c2_apply g x).symm⟩

/-- Sign has the section which sends minus one to the transposition `(0 1)`. -/
def signSection : C2 →* S3 where
  toFun u := if u = 1 then 1 else Equiv.swap 0 1
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp

@[simp] theorem sign_signSection (u : C2) :
    Equiv.Perm.sign (signSection u) = u := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    simp [signSection]

/-- In `S₃`, every even permutation is a single commutator. -/
theorem even_is_commutator : ∀ g : S3, Equiv.Perm.sign g = 1 →
    ∃ a b : S3, ⁅a, b⁆ = g := by
  decide

/-- Thus the kernel of sign is exactly the commutator subgroup. -/
theorem commutator_s3 : commutator S3 = (Equiv.Perm.sign : S3 →* C2).ker := by
  apply le_antisymm (Abelianization.commutator_subset_ker Equiv.Perm.sign)
  intro g hg
  obtain ⟨a, b, rfl⟩ := even_is_commutator g hg
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

/-- Every homomorphism from `S₃` to an abelian group factors through sign. -/
theorem sign_factor {H : Type*} [CommGroup H] (f : S3 →* H) (g : S3) :
    f (signSection (Equiv.Perm.sign g)) = f g := by
  have hker : (Equiv.Perm.sign : S3 →* C2).ker ≤ f.ker := by
    rw [← commutator_s3]
    exact Abelianization.commutator_subset_ker f
  have h : g * (signSection (Equiv.Perm.sign g))⁻¹ ∈
      (Equiv.Perm.sign : S3 →* C2).ker := by
    simp [MonoidHom.mem_ker]
  have hf : f g = f (signSection (Equiv.Perm.sign g)) := by
    simpa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] using hker h
  exact hf.symm

/-- Syntax for finite products of the two cyclic groups. The syntactic
presentation avoids making an arbitrary choice of a skeleton. -/
inductive AbelianWord
  | unit
  | c2
  | c3
  | prod (A B : AbelianWord)
  deriving DecidableEq

namespace AbelianWord

abbrev Carrier : AbelianWord → Type
  | .unit => PUnit
  | .c2 => C2
  | .c3 => C3
  | .prod A B => A.Carrier × B.Carrier

instance carrierCommGroup : (A : AbelianWord) → CommGroup A.Carrier
  | .unit => inferInstanceAs (CommGroup PUnit)
  | .c2 => inferInstanceAs (CommGroup C2)
  | .c3 => inferInstanceAs (CommGroup C3)
  | .prod A B => by
    letI := carrierCommGroup A
    letI := carrierCommGroup B
    exact inferInstanceAs (CommGroup (A.Carrier × B.Carrier))

instance carrierFinite : (A : AbelianWord) → Finite A.Carrier
  | .unit => inferInstanceAs (Finite PUnit)
  | .c2 => inferInstanceAs (Finite C2)
  | .c3 => inferInstanceAs (Finite C3)
  | .prod A B => by
    let := carrierFinite A
    let := carrierFinite B
    exact inferInstanceAs (Finite (A.Carrier × B.Carrier))

end AbelianWord

/-- Syntax for the finite products of `S₃`, `C₂`, and `C₃` in the paper. -/
inductive GroupWord
  | s3
  | ab (A : AbelianWord)
  | prod (G H : GroupWord)
  deriving DecidableEq

namespace GroupWord

abbrev Carrier : GroupWord → Type
  | .s3 => S3
  | .ab A => A.Carrier
  | .prod G H => G.Carrier × H.Carrier

instance carrierGroup : (G : GroupWord) → Group G.Carrier
  | .s3 => inferInstanceAs (Group S3)
  | .ab A => inferInstanceAs (Group A.Carrier)
  | .prod G H => by
    letI := carrierGroup G
    letI := carrierGroup H
    exact inferInstanceAs (Group (G.Carrier × H.Carrier))

instance carrierFinite : (G : GroupWord) → Finite G.Carrier
  | .s3 => inferInstanceAs (Finite S3)
  | .ab A => inferInstanceAs (Finite A.Carrier)
  | .prod G H => by
    let := carrierFinite G
    let := carrierFinite H
    exact inferInstanceAs (Finite (G.Carrier × H.Carrier))

/-- Abelianization replaces each `S₃` factor by `C₂`. -/
def reflect : GroupWord → AbelianWord
  | .s3 => .c2
  | .ab A => A
  | .prod G H => .prod G.reflect H.reflect

/-- The quotient homomorphism, assembled from signs and identities. -/
def quotient : (G : GroupWord) → G.Carrier →* G.reflect.Carrier
  | .s3 => Equiv.Perm.sign
  | .ab A => MonoidHom.id A.Carrier
  | .prod G H => (quotient G).prodMap (quotient H)

/-- Every quotient has a group homomorphism section. -/
def sectionHom : (G : GroupWord) → G.reflect.Carrier →* G.Carrier
  | .s3 => signSection
  | .ab A => MonoidHom.id A.Carrier
  | .prod G H => (sectionHom G).prodMap (sectionHom H)

@[simp] theorem quotient_section (G : GroupWord) (x : G.reflect.Carrier) :
    quotient G (sectionHom G x) = x := by
  induction G with
  | s3 => exact sign_signSection x
  | ab A => rfl
  | prod G H ihG ihH => exact Prod.ext (ihG x.1) (ihH x.2)

theorem quotient_surjective (G : GroupWord) : Function.Surjective (quotient G) :=
  fun x => ⟨sectionHom G x, quotient_section G x⟩

/-- A homomorphism to any abelian group cannot distinguish an element
from the chosen lift of its image in the quotient. -/
theorem section_quotient {H : Type*} [CommGroup H] :
    ∀ (G : GroupWord) (f : G.Carrier →* H) (x : G.Carrier),
      f (sectionHom G (quotient G x)) = f x := by
  intro G
  induction G with
  | s3 => exact fun f x => sign_factor f x
  | ab A => exact fun f x => rfl
  | prod G K ihG ihK =>
    intro f x
    change f (sectionHom G (quotient G x.1), sectionHom K (quotient K x.2)) = f x
    have hG := ihG (f.comp (MonoidHom.inl G.Carrier K.Carrier)) x.1
    have hK := ihK (f.comp (MonoidHom.inr G.Carrier K.Carrier)) x.2
    change f (sectionHom G (quotient G x.1), 1) = f (x.1, 1) at hG
    change f (1, sectionHom K (quotient K x.2)) = f (1, x.2) at hK
    calc
      f (sectionHom G (quotient G x.1), sectionHom K (quotient K x.2)) =
          f (sectionHom G (quotient G x.1), 1) *
            f (1, sectionHom K (quotient K x.2)) := by
        rw [← map_mul]
        simp
      _ = f (x.1, 1) * f (1, x.2) := by rw [hG, hK]
      _ = f x := by rw [← map_mul]; simp

/-- The factor through the abelianization quotient. -/
def factor {H : Type*} [CommGroup H] {G : GroupWord} (f : G.Carrier →* H) :
    G.reflect.Carrier →* H := f.comp (sectionHom G)

@[simp] theorem factor_comp_quotient {H : Type*} [CommGroup H]
    {G : GroupWord} (f : G.Carrier →* H) :
    (factor f).comp (quotient G) = f :=
  MonoidHom.ext (section_quotient G f)

/-- Uniqueness in the universal property of abelianization. -/
theorem factor_unique {H : Type*} [CommGroup H] {G : GroupWord}
    (f : G.Carrier →* H) (g : G.reflect.Carrier →* H)
    (hg : g.comp (quotient G) = f) : g = factor f := by
  ext x
  have h := DFunLike.congr_fun hg (sectionHom G x)
  simpa [factor, MonoidHom.comp_apply] using h

end GroupWord
end Counterexample
