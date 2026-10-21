import SemigenericEPPA.Structure.EffectiveGeometry
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Prod

/-!
# Exact quotient E-index action on one fixed equal-fibre carrier

The nontrivial-G relative group-lift theorem takes an H-action on
real auxiliary labels and an H-action on their ACTUAL E-class
quotient, with equality [h x] = h[x]. The fixed factorial
replicated-fibre construction instead first returns an H-action
iota on the original E-part label set I and an H-action rhoFull
on the fixed carrier I×Fin M, satisfying
  (rhoFull(h)(i,u)).1 = iota(h)(i).

If the actual witness geometry B has E exactly equality of its
first coordinates, and its fixed fibre Fin M is inhabited, the
two index sorts I and Quotient B.part are canonically equivalent.
Transporting iota across this equivalence produces a STRICT group
action on the actual Quotient B.part, without choosing unrelated
permutations for separate h. The compatibility equation on every
witness label follows from the first-coordinate equation.

The result requires no effective F-invariance and is valid for
nontrivial noncommutative effective groups. It is the quotient
action interface connecting the factorial label lift to the
reference-twisted full effective H-lift.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {I : Type v}
variable {H : Type w} [Group H]
variable {s : AffineAntiInvolution G}

/-- The actual quotient E-sort of any nonempty equal-fibre
geometry is canonically equivalent to its original part-index
sort. The chosen zero in Fin M is only a representative, not
additional geometry. -/
noncomputable def fixedFibreQuotientEquiv
    (M : ℕ) (hpos : 0 < M)
    (B : EffectiveGeometry s (I × Fin M))
    (hPart : ∀ z w : I × Fin M,
      B.part z w ↔ z.1 = w.1) :
    Quotient B.part ≃ I where
  toFun := Quotient.lift Prod.fst (by
    intro z w hz
    exact (hPart z w).mp hz)
  invFun := fun i => Quotient.mk B.part (i, ⟨0, hpos⟩)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ z =>
      apply Quotient.sound
      exact (hPart _ _).mpr rfl
  right_inv := by
    intro i
    rfl

/-- Conjugate one strict group action on the fixed part-index
labels into a strict action on the ACTUAL quotient of the
effective witness E-relation, with no F assumptions. -/
noncomputable def fixedFibreQuotientGroupAction
    (M : ℕ) (hpos : 0 < M)
    (B : EffectiveGeometry s (I × Fin M))
    (hPart : ∀ z w : I × Fin M,
      B.part z w ↔ z.1 = w.1)
    (iota : H →* Equiv.Perm I) :
    H →* Equiv.Perm (Quotient B.part) := by
  let e : Quotient B.part ≃ I :=
    fixedFibreQuotientEquiv M hpos B hPart
  exact {
    toFun := fun h => (e.trans (iota h)).trans e.symm
    map_one' := by
      apply Equiv.ext
      intro q
      change e.symm (iota (1 : H) (e q)) = q
      simp
    map_mul' := by
      intro k h
      apply Equiv.ext
      intro q
      change e.symm (iota (k * h) (e q)) =
        e.symm (iota k (e (e.symm (iota h (e q)))))
      rw [map_mul, e.apply_symm_apply]
      rfl
  }

/-- An H-action on the fixed auxiliary labels compatible with
the old part-index action induces an exactly compatible strict
H-action on the genuine quotient E-classes. No preservation of
effective old colours outside the selected S is assumed. -/
theorem fixedFibreQuotientGroupAction_compatible
    (M : ℕ) (hpos : 0 < M)
    (B : EffectiveGeometry s (I × Fin M))
    (hPart : ∀ z w : I × Fin M,
      B.part z w ↔ z.1 = w.1)
    (iota : H →* Equiv.Perm I)
    (rhoFull : H →* Equiv.Perm (I × Fin M))
    (hIndex : ∀ (h : H) (z : I × Fin M),
      (rhoFull h z).1 = iota h z.1)
    (h : H) (z : I × Fin M) :
    Quotient.mk B.part (rhoFull h z) =
      fixedFibreQuotientGroupAction M hpos B hPart iota h
        (Quotient.mk B.part z) := by
  let e : Quotient B.part ≃ I :=
    fixedFibreQuotientEquiv M hpos B hPart
  apply e.injective
  change (rhoFull h z).1 = iota h z.1
  exact hIndex h z

/-- Consumer interface for the actual quotient of a fixed
nonempty equal-fibre witness. Unlike the index-labelled action,
the output has precisely the Quotient E type expected by the
two-layer valuation witness constructors. -/
theorem exists_fixedFibreQuotientGroupAction
    (M : ℕ) (hpos : 0 < M)
    (B : EffectiveGeometry s (I × Fin M))
    (hPart : ∀ z w : I × Fin M,
      B.part z w ↔ z.1 = w.1)
    (iota : H →* Equiv.Perm I)
    (rhoFull : H →* Equiv.Perm (I × Fin M))
    (hIndex : ∀ (h : H) (z : I × Fin M),
      (rhoFull h z).1 = iota h z.1) :
    ∃ iotaQ : H →* Equiv.Perm (Quotient B.part),
      ∀ (h : H) (z : I × Fin M),
        Quotient.mk B.part (rhoFull h z) =
          iotaQ h (Quotient.mk B.part z) := by
  exact ⟨fixedFibreQuotientGroupAction M hpos B hPart iota,
    fixedFibreQuotientGroupAction_compatible
      M hpos B hPart iota rhoFull hIndex⟩

end SemigenericEPPA
