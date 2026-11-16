import Mathlib.Data.List.Infix
import Mathlib.Data.Nat.Basic

/-!
# Finite binary words and branches

Words are finite lists of bits. As in the Agda development (`gist.RealCohesion.Cylinders`),
bits are appended at the end: `snoc s b` is `s ⌢ b`, and `restrict α n` is `α ↾ n`, the
first `n` bits of an infinite sequence. The prefix order is `<+:`.
-/

namespace PointlessEnd

/-- Finite binary words. -/
abbrev Word := List Bool

/-- `s ⌢ b`: append one bit at the end. -/
def snoc (s : Word) (b : Bool) : Word := s ++ [b]

/-- `α ↾ n`: the first `n` bits of `α`. -/
def restrict (α : ℕ → Bool) : ℕ → Word
  | 0 => []
  | n + 1 => snoc (restrict α n) (α n)

/-- Two words are compatible when one is a prefix of the other. -/
def Compat (s w : Word) : Prop := s <+: w ∨ w <+: s

theorem prefix_snoc (s : Word) (b : Bool) : s <+: snoc s b := List.prefix_append _ _

@[simp] theorem length_snoc (s : Word) (b : Bool) : (snoc s b).length = s.length + 1 := by
  simp [snoc]

@[simp] theorem length_restrict (α : ℕ → Bool) : ∀ n, (restrict α n).length = n
  | 0 => rfl
  | n + 1 => by simp [restrict, length_restrict α n]

theorem restrict_prefix (α : ℕ → Bool) {m n : ℕ} (h : m ≤ n) : restrict α m <+: restrict α n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (prefix_snoc _ _)
    · rw [le_antisymm h h']

/-- Prefixes of a common word are comparable. -/
theorem compat_of_prefix {s w v : Word} (hs : s <+: v) (hw : w <+: v) : Compat s w :=
  List.prefix_or_prefix_of_prefix hs hw

theorem compat_symm {s w : Word} (h : Compat s w) : Compat w s := h.symm

/-- Extensions of a word incompatible with `s` stay incompatible with `s`. -/
theorem incompat_mono {s w u : Word} (hw : ¬ Compat s w) (hwu : w <+: u) : ¬ Compat s u := by
  rintro (h | h)
  · exact hw (compat_of_prefix h hwu)
  · exact hw (Or.inr (hwu.trans h))

/-- If `s` is not a prefix of `w`, some extension of `w` is incompatible with `s`. -/
theorem exists_ext_incompat {s w : Word} (h : ¬ s <+: w) : ∃ u, w <+: u ∧ ¬ Compat s u := by
  by_cases hc : Compat s w
  · rcases hc with hc | hc
    · exact absurd hc h
    · obtain ⟨r, rfl⟩ := hc
      cases r with
      | nil => exact absurd (by simp : w ++ [] <+: w) h
      | cons b r =>
        refine ⟨w ++ [!b], List.prefix_append _ _, ?_⟩
        rintro (h1 | h1)
        · rw [List.prefix_append_right_inj] at h1
          simp [List.cons_prefix_cons] at h1
        · rw [List.prefix_append_right_inj] at h1
          simp [List.cons_prefix_cons] at h1
  · exact ⟨w, List.prefix_refl _, hc⟩

/-- A prefix of `snoc s b` is a prefix of `s` or equal to `snoc s b`. -/
theorem prefix_snoc_iff {w s : Word} {b : Bool} : w <+: snoc s b ↔ w <+: s ∨ w = snoc s b := by
  constructor
  · intro h
    rcases compat_of_prefix h (prefix_snoc s b) with h' | h'
    · exact Or.inl h'
    · have h1 := h'.length_le
      have h2 := h.length_le
      simp only [length_snoc] at h2
      rcases Nat.lt_or_ge s.length w.length with h3 | h3
      · right
        exact List.IsPrefix.eq_of_length h (by simp only [length_snoc]; omega)
      · left
        obtain rfl := List.IsPrefix.eq_of_length h' (by omega)
        exact List.prefix_refl _
  · rintro (h | rfl)
    · exact h.trans (prefix_snoc _ _)
    · exact List.prefix_refl _

/-- A proper extension of `s` extends one of its two children. -/
theorem snoc_prefix_of_ne {s u : Word} (h : s <+: u) (hne : u ≠ s) :
    ∃ b, snoc s b <+: u := by
  obtain ⟨r, rfl⟩ := h
  cases r with
  | nil => exact absurd (by simp) hne
  | cons b r => exact ⟨b, by simp [snoc]⟩

theorem snoc_ne_snoc {s : Word} : snoc s false ≠ snoc s true := by simp [snoc]

/-- The two children of a word are incompatible. -/
theorem not_compat_children (s : Word) : ¬ Compat (snoc s false) (snoc s true) := by
  rintro (h | h)
  · exact snoc_ne_snoc (List.IsPrefix.eq_of_length h (by simp))
  · exact snoc_ne_snoc (List.IsPrefix.eq_of_length h (by simp)).symm

/-- The branch `α` passes through `w` iff `w = α ↾ |w|`. -/
theorem prefix_restrict_of_compat {α : ℕ → Bool} {w : Word} {n : ℕ}
    (h : w <+: restrict α n) : w = restrict α w.length := by
  have hl : w.length ≤ n := by simpa using h.length_le
  have h2 : restrict α w.length <+: restrict α n := restrict_prefix α hl
  rcases compat_of_prefix h h2 with h3 | h3
  · exact List.IsPrefix.eq_of_length h3 (by simp)
  · exact (List.IsPrefix.eq_of_length h3 (by simp)).symm

end PointlessEnd
