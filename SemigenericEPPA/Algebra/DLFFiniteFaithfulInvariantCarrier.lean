import SemigenericEPPA.Algebra.DLFFiniteInvariantOrbitCarrier
import Mathlib.Data.Fintype.EquivFin

/-!
# A finite faithful permutation group has a finite faithful invariant carrier

A finite subgroup of automorphisms of an infinite structure need not
act faithfully on an arbitrarily chosen finite induced substructure.

Here we prove that it DOES have a finite invariant set on which its
action is faithful: for every distinct pair of group elements choose
one point on which their permutations disagree, then close the
finite witness set under the entire finite group.

No point is chosen for an empty witness family. Thus the theorem
also works on empty carrier types and for trivial finite groups.
This is needed for exporting dense locally finite obstruction
arguments to true finite faithful original-language action pairs.
-/

namespace SemigenericEPPA

universe u
variable {V : Type u}

/-- For any two distinct actual permutations there is a vertex
where they differ. We use this on the subgroup subtype to avoid
assuming that the ambient vertex type is inhabited. -/
private theorem finiteGroup_perms_distinguished
    (H : Subgroup (Equiv.Perm V))
    (a b : H) (hab : a ≠ b) :
    ∃ x : V, a.val x ≠ b.val x := by
  classical
  by_contra h
  apply hab
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_contra hne
  exact h ⟨x, hne⟩

/-- An ACTUAL finite permutation subgroup admits one finite
invariant vertex subset on which all group elements remain
pairwise distinguishable, even if the ambient carrier is infinite.
The subgroup is not replaced by an unrelated isomorphic action. -/
theorem finiteGroup_exists_finiteFaithfulInvariantCarrier
    (H : Subgroup (Equiv.Perm V))
    [Finite H] :
    ∃ F : Finset V,
      (∀ h : H, ∀ x : V, x ∈ F → h.val x ∈ F) ∧
      (∀ h k : H, (∀ x : V, x ∈ F →
        h.val x = k.val x) → h = k) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  let Pairs := {p : H × H // p.1 ≠ p.2}
  letI : Finite Pairs := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype Pairs := Fintype.ofFinite Pairs
  let w : Pairs → V := fun p =>
    Classical.choose
      (finiteGroup_perms_distinguished H p.val.1 p.val.2 p.property)
  have hw (p : Pairs) :
      p.val.1.val (w p) ≠ p.val.2.val (w p) :=
    Classical.choose_spec
      (finiteGroup_perms_distinguished H p.val.1 p.val.2 p.property)
  let seeds : Finset V := Finset.univ.image w
  let F : Finset V := finiteGroupOrbitFinset H seeds
  refine ⟨F, ?_, ?_⟩
  · intro h x hx
    exact finiteGroupOrbitFinset_invariant H seeds h x hx
  · intro h k heq
    by_contra hne
    let p : Pairs := ⟨(h, k), hne⟩
    have hp : w p ∈ seeds := by
      apply Finset.mem_image.mpr
      exact ⟨p, Finset.mem_univ _, rfl⟩
    have hpF : w p ∈ F :=
      finiteGroupOrbitFinset_contains H seeds hp
    exact hw p (heq (w p) hpF)

end SemigenericEPPA
