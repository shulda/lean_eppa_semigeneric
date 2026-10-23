import SemigenericEPPA.Algebra.DLFDirectedPermUnionDensity
import SemigenericEPPA.Algebra.DLFAscendingFiniteSubgroups
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Algebraic dense locally finite subgroup criterion for a finite group tower

Assume an honest countable INCREASING sequence Kₙ of FINITE
subgroups of the same actual automorphism group A≤Perm(V).
Assume every target automorphism a∈A can be matched on every
finite set of points by a member of one Kₙ. Then the ONE
subgroup L=⋃ₙKₙ is:

* a subgroup of A (not merely of all permutations);
* dense in A in the finite-restriction sense;
* locally finite: each finitely generated subgroup of L is finite.

The density conclusion uses the companion directed-union lemma.
The local finiteness conclusion builds, inside L, an ascending
tower of subgroups consisting of the old Kₙ, then applies the
separately certified ascending-finite-subgroups theorem.

This is an abstract algebraic bridge for the positive DLF theorem,
not a construction of the actual tower of original-language
automorphisms or a theorem about the pointwise-convergence topology.
-/

namespace SemigenericEPPA

universe u
variable {V : Type u}

/-- A finite-group tower which approximates all target automorphisms
on all finite vertex sets yields a single locally finite subgroup
with exactly the expected finite-restriction density property. -/
theorem exists_locallyFinite_denseByFiniteRestrictions_of_tower
    (A : Subgroup (Equiv.Perm V))
    (K : ℕ → Subgroup (Equiv.Perm V))
    (hmono : Monotone K)
    (hFinite : ∀ n, Finite (K n))
    (hKA : ∀ n, K n ≤ A)
    (hApprox : ∀ (a : A) (F : Finset V),
      ∃ n : ℕ, ∃ k : K n,
        ∀ (x : V), x ∈ F → k.val x = a.val x) :
    ∃ L : Subgroup (Equiv.Perm V),
      L ≤ A ∧
      DenseByFiniteRestrictions A L ∧
      EveryFinitelyGeneratedSubgroupFinite L := by
  let L : Subgroup (Equiv.Perm V) :=
    ascendingUnionPermSubgroup K hmono
  have hDense : DenseByFiniteRestrictions A L :=
    denseByFiniteRestrictions_ascendingUnion A K hmono hKA hApprox
  let Kinside : ℕ → Subgroup L :=
    fun n => (K n).comap L.subtype
  have hInsideMono : Monotone Kinside := by
    intro n m hnm g hg
    exact hmono hnm hg
  have hInsideFinite : ∀ n, Finite (Kinside n) := by
    intro n
    letI : Finite (K n) := hFinite n
    have hinj : Function.Injective
        (fun z : Kinside n => (⟨z.val.val, z.property⟩ : K n)) := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg Subtype.val hxy
    exact Finite.of_injective _ hinj
  have hInsideCover : ∀ k : L, ∃ n, k ∈ Kinside n := by
    intro k
    obtain ⟨n, hn⟩ := k.property
    exact ⟨n, hn⟩
  have hLocal : EveryFinitelyGeneratedSubgroupFinite L :=
    locallyFinite_of_ascendingFiniteSubgroups
      Kinside hInsideMono hInsideFinite hInsideCover
  exact ⟨L, hDense.1, hDense, hLocal⟩

end SemigenericEPPA
