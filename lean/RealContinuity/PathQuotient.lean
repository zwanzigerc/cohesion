import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-!
# The external path-component quotient and its iterates

`Q X` is the set of ordinary path components of `X` with the QUOTIENT topology
(mathlib's `ZerothHomotopy`). It is an external topological invariant used to
build a map into a constant sheaf; it is never identified with the topos's `Π`.

The iterates are defined inner-first: `Q^(n+1) X = Q^n (Q X)` and
`η^(n+1)_X = η^n_(Q X) ∘ η_X`. Naturality of `η^n` then gives persistence
of equalities to larger heights without any identification of `Q^n (Q X)`
with `Q (Q^n X)`.
-/

noncomputable section

open Topology

namespace RealContinuity

universe u

/-- The path-component quotient with its quotient topology. -/
abbrev Q (X : TopCat.{u}) : TopCat.{u} := TopCat.of (ZerothHomotopy X)

/-- The quotient map `η_X : X → Q X`. -/
def eta (X : TopCat.{u}) : C(X, Q X) :=
  ⟨ZerothHomotopy.mk, ZerothHomotopy.isQuotientMap_mk.continuous⟩

theorem eta_surjective (X : TopCat.{u}) : Function.Surjective (eta X) :=
  ZerothHomotopy.mk_surjective

theorem isQuotientMap_eta (X : TopCat.{u}) : IsQuotientMap (eta X) :=
  ZerothHomotopy.isQuotientMap_mk

theorem eta_eq_of_joined {X : TopCat.{u}} {x y : X} (h : Joined x y) : eta X x = eta X y :=
  ZerothHomotopy.sound h.somePath

theorem joined_of_eta_eq {X : TopCat.{u}} {x y : X} (h : eta X x = eta X y) : Joined x y :=
  Quotient.exact h

theorem eta_eq_iff {X : TopCat.{u}} {x y : X} : eta X x = eta X y ↔ Joined x y :=
  ⟨joined_of_eta_eq, eta_eq_of_joined⟩

/-- Continuous functoriality of `Q`. -/
def Qmap {X Y : TopCat.{u}} (f : C(X, Y)) : C(Q X, Q Y) where
  toFun := ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x))
    (fun _ _ p => ZerothHomotopy.sound (p.map f.continuous))
  continuous_toFun := by
    rw [(isQuotientMap_eta X).continuous_iff]
    exact (eta Y).continuous.comp f.continuous

@[simp]
theorem Qmap_eta {X Y : TopCat.{u}} (f : C(X, Y)) (x : X) :
    Qmap f (eta X x) = eta Y (f x) := rfl

theorem Qmap_id (X : TopCat.{u}) (z : Q X) : Qmap (ContinuousMap.id X) z = z := by
  obtain ⟨x, rfl⟩ := eta_surjective X z
  rfl

theorem Qmap_comp {X Y Z : TopCat.{u}} (g : C(Y, Z)) (f : C(X, Y)) (z : Q X) :
    Qmap (g.comp f) z = Qmap g (Qmap f z) := by
  obtain ⟨x, rfl⟩ := eta_surjective X z
  rfl

/-- Inner-first iterates `Q^n`. -/
def Qiter : ℕ → TopCat.{u} → TopCat.{u}
  | 0, X => X
  | n + 1, X => Qiter n (Q X)

/-- The iterated quotient maps `η^n_X : X → Q^n X`. -/
def etaIter : (n : ℕ) → (X : TopCat.{u}) → C(X, Qiter n X)
  | 0, X => ContinuousMap.id X
  | n + 1, X => (etaIter n (Q X)).comp (eta X)

/-- The iterated functorial action `Q^n f`. -/
def QmapIter : (n : ℕ) → {X Y : TopCat.{u}} → C(X, Y) → C(Qiter n X, Qiter n Y)
  | 0, _, _, f => f
  | n + 1, _, _, f => QmapIter n (Qmap f)

/-- Naturality of `η^n`. -/
theorem QmapIter_etaIter : ∀ (n : ℕ) {X Y : TopCat.{u}} (f : C(X, Y)) (x : X),
    QmapIter n f (etaIter n X x) = etaIter n Y (f x)
  | 0, _, _, _, _ => rfl
  | n + 1, X, Y, f, x => by
    change QmapIter n (Qmap f) (etaIter n (Q X) (eta X x)) =
      etaIter n (Q Y) (eta Y (f x))
    rw [QmapIter_etaIter n (Qmap f) (eta X x), Qmap_eta]

/-- `η^(n+1)` factors through `η^n`: `η^(n+1)_X = Q^n(η_X) ∘ η^n_X`. -/
theorem etaIter_succ_apply (n : ℕ) (X : TopCat.{u}) (x : X) :
    etaIter (n + 1) X x = QmapIter n (eta X) (etaIter n X x) := by
  rw [QmapIter_etaIter]
  rfl

/-- Equality at height `n` persists at height `n + 1`. -/
theorem etaIter_succ_eq {n : ℕ} {X : TopCat.{u}} {x y : X}
    (h : etaIter n X x = etaIter n X y) : etaIter (n + 1) X x = etaIter (n + 1) X y := by
  rw [etaIter_succ_apply, etaIter_succ_apply, h]

/-- Equality at height `n` persists at every larger height. -/
theorem etaIter_eq_of_le {n m : ℕ} (hnm : n ≤ m) {X : TopCat.{u}} {x y : X}
    (h : etaIter n X x = etaIter n X y) : etaIter m X x = etaIter m X y := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact etaIter_succ_eq ih

/-- Separation at a height implies separation at every smaller height. -/
theorem etaIter_ne_of_le {n m : ℕ} (hnm : n ≤ m) {X : TopCat.{u}} {x y : X}
    (h : etaIter m X x ≠ etaIter m X y) : etaIter n X x ≠ etaIter n X y :=
  fun h' => h (etaIter_eq_of_le hnm h')

/-- Equality at a height is preserved by continuous maps. -/
theorem etaIter_map_eq {n : ℕ} {X Y : TopCat.{u}} (f : C(X, Y)) {x y : X}
    (h : etaIter n X x = etaIter n X y) : etaIter n Y (f x) = etaIter n Y (f y) := by
  rw [← QmapIter_etaIter, ← QmapIter_etaIter, h]

end RealContinuity
