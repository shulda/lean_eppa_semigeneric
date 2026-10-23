import Mathlib.Algebra.Group.End

/-!
# Faithfulness of an exact relative finite H-action extension

The semi-coherent extension property requires GROUP EMBEDDINGS, not
merely strict group homomorphisms. The actual relative raw witness
provides a strict homomorphism from H to whole-witness permutations,
extending the genuine old H-action on an induced subset S.

If the old action H→Perm(S) was faithful and its inclusion into the
new witness is injective, the extended whole-witness action is
automatically faithful. This is a pure group-action argument:
any two new permutations that agree on all new vertices agree on
the distinguished embedded S, and hence their old permutations
coincide. No order-two or orbit hypothesis is needed.

This lemma is the exact faithfulness interface required to turn
relative safe raw EPPA into the finite-action-pair extension step.
It does NOT itself construct the witness or prove that involutions
of the extended action remain globally safe.
-/

namespace SemigenericEPPA

universe u v w
variable {H : Type u} [Group H]
variable {A : Type v} {W : Type w}

/-- Faithful old H action plus an injective old embedding forces
EVERY strict lifted action on the same image to be faithful. -/
theorem faithfulRelativeGroupLift_of_oldAction
    (S : Set A)
    (e : A → W)
    (he : Function.Injective e)
    (rhoS : H →* Equiv.Perm S)
    (hFaithful : Function.Injective rhoS)
    (lift : H →* Equiv.Perm W)
    (hOld : ∀ (h : H) (x : S),
      lift h (e x.val) = e (rhoS h x).val) :
    Function.Injective lift := by
  intro h k hlift
  apply hFaithful
  apply Equiv.ext
  intro x
  apply Subtype.ext
  apply he
  calc
    e (rhoS h x).val = lift h (e x.val) := (hOld h x).symm
    _ = lift k (e x.val) := by rw [hlift]
    _ = e (rhoS k x).val := hOld k x

end SemigenericEPPA
