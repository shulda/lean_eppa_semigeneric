import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Tactic.Group

/-!
# Relative DLF cover: an exact finite-group coset action

The finitary involution-killing extension used in the relative DLF
construction begins with a finite group Q and a subgroup H. One
invariant layer of its auxiliary graph is the left-coset set Q/H.
An element t fixes a coset qH precisely when q⁻¹*t*q lies in H.
Thus any t not conjugate into H has no fixed coset.

We formalize this without assuming H normal: the quotient uses the
literal left-coset equivalence x~y iff x⁻¹*y∈H, not the group
quotient Q/H (which is only a group for normal H). Left translation
produces an actual strict group homomorphism into its permutation
group. No finiteness or involution hypothesis is needed for the
stabilizer equivalence.

This is the first graph-action input for the later finite
F₂ edge-chain parity cover. It does NOT assert that the whole
graph involution action is free on edges or that the cover exists.
-/

namespace SemigenericEPPA

universe u
variable {Q : Type u} [Group Q]

namespace RelativeDLF

/-- Equivalence relation of left cosets qH for an arbitrary subgroup
H, expressed without any normality assumption. -/
def leftCosetSetoid (H : Subgroup Q) : Setoid Q where
  r x y := x⁻¹ * y ∈ H
  iseqv := by
    constructor
    · intro x
      simpa using H.one_mem
    · intro x y hxy
      have hInv := H.inv_mem hxy
      have hEq : (x⁻¹ * y)⁻¹ = y⁻¹ * x := by group
      rw [hEq] at hInv
      exact hInv
    · intro x y z hxy hyz
      have hProd : x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) := by group
      rw [hProd]
      exact H.mul_mem hxy hyz

/-- Left-coset type of an arbitrary subgroup, with no normality. -/
abbrev LeftCosets (H : Subgroup Q) := Quotient (leftCosetSetoid H)

/-- The left translation qH ↦ (gq)H is well-defined even when
the subgroup H is nonnormal. -/
def leftCosetTranslate (H : Subgroup Q) (g : Q) :
    LeftCosets H → LeftCosets H :=
  Quotient.lift (fun x : Q =>
      Quotient.mk (leftCosetSetoid H) (g * x))
    (by
      intro x y hxy
      apply Quotient.sound
      change (g * x)⁻¹ * (g * y) ∈ H
      have hEq : (g * x)⁻¹ * (g * y) = x⁻¹ * y := by group
      rw [hEq]
      exact hxy)

@[simp] theorem leftCosetTranslate_mk
    (H : Subgroup Q) (g x : Q) :
    leftCosetTranslate H g (Quotient.mk (leftCosetSetoid H) x) =
      Quotient.mk (leftCosetSetoid H) (g * x) := rfl

@[simp] theorem leftCosetTranslate_one
    (H : Subgroup Q) (x : LeftCosets H) :
    leftCosetTranslate H 1 x = x := by
  induction x using Quotient.inductionOn with
  | _ q => simp

theorem leftCosetTranslate_mul
    (H : Subgroup Q) (g h : Q) (x : LeftCosets H) :
    leftCosetTranslate H (g * h) x =
      leftCosetTranslate H g (leftCosetTranslate H h x) := by
  induction x using Quotient.inductionOn with
  | _ q => simp [mul_assoc]

/-- The actual bijection implementing left multiplication. -/
def leftCosetPerm (H : Subgroup Q) (g : Q) :
    Equiv.Perm (LeftCosets H) where
  toFun := leftCosetTranslate H g
  invFun := leftCosetTranslate H g⁻¹
  left_inv := by
    intro x
    calc
      leftCosetTranslate H g⁻¹ (leftCosetTranslate H g x) =
          leftCosetTranslate H (g⁻¹ * g) x :=
        (leftCosetTranslate_mul H g⁻¹ g x).symm
      _ = x := by simp
  right_inv := by
    intro x
    calc
      leftCosetTranslate H g (leftCosetTranslate H g⁻¹ x) =
          leftCosetTranslate H (g * g⁻¹) x :=
        (leftCosetTranslate_mul H g g⁻¹ x).symm
      _ = x := by simp

/-- Strict homomorphic action of Q on left cosets of H. -/
def leftCosetAction (H : Subgroup Q) :
    Q →* Equiv.Perm (LeftCosets H) where
  toFun := leftCosetPerm H
  map_one' := by
    apply Equiv.ext
    intro x
    exact leftCosetTranslate_one H x
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro x
    exact leftCosetTranslate_mul H g h x

/-- The stabilizer of qH under left multiplication is exactly
qHq⁻¹, written in the equivalent conjugation orientation. -/
theorem leftCosetAction_fixed_iff
    (H : Subgroup Q) (g q : Q) :
    leftCosetAction H g
        (Quotient.mk (leftCosetSetoid H) q) =
      Quotient.mk (leftCosetSetoid H) q ↔
        q⁻¹ * g * q ∈ H := by
  change (Quotient.mk (leftCosetSetoid H) (g * q) =
      Quotient.mk (leftCosetSetoid H) q) ↔
        q⁻¹ * g * q ∈ H
  constructor
  · intro h
    have hh : (g * q)⁻¹ * q ∈ H := Quotient.exact h
    have hInv := H.inv_mem hh
    have heq : ((g * q)⁻¹ * q)⁻¹ = q⁻¹ * g * q := by group
    rwa [heq] at hInv
  · intro h
    apply Quotient.sound
    change (g * q)⁻¹ * q ∈ H
    have heq : (q⁻¹ * g * q)⁻¹ = (g * q)⁻¹ * q := by group
    rw [← heq]
    exact H.inv_mem h

/-- No element not conjugate into H can fix ANY coset. This is
the precise free-vertex action condition on the Q/H layer of
the relative involution-killing graph. -/
theorem leftCosetAction_no_fixed_of_no_conjugate
    (H : Subgroup Q) (g : Q)
    (hNoConjugate : ∀ q : Q, q⁻¹ * g * q ∉ H)
    (x : LeftCosets H) :
    leftCosetAction H g x ≠ x := by
  induction x using Quotient.inductionOn with
  | _ q =>
    intro hx
    exact hNoConjugate q
      ((leftCosetAction_fixed_iff H g q).mp hx)

end RelativeDLF

end SemigenericEPPA
