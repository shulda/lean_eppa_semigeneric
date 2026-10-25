import SemigenericEPPA.Algebra.DLFAscendingFiniteSubgroups

/-!
# Finite subgroup containing any prescribed finite subset in a locally finite group

The negative DLF direction starts with an actual locally finite
subgroup L of the automorphism group of a homogeneous original
R1–R3 structure. Given finitely many automorphisms from L,
their generated subgroup is finite BY THE DEFINITION of local
finiteness, and contains all prescribed automorphisms.

This extracts an actual finite subgroup in Lean without introducing
a chosen finite group action, recentering affine colours, or assuming
that a permutation extending an order-two partial automorphism
itself has order two.

It is a small prerequisite for transferring finite negative
delta-profile / parity obstructions to countable DLF groups.
-/

namespace SemigenericEPPA

universe u
variable {Q : Type u} [Group Q]

/-- Every finite set of elements of a locally finite group is
contained in an ACTUAL finite subgroup. -/
theorem locallyFinite_exists_finiteSubgroup_covering
    (hLF : EveryFinitelyGeneratedSubgroupFinite Q)
    (s : Finset Q) :
    ∃ H : Subgroup Q,
      Finite H ∧ ∀ q : Q, q ∈ s → q ∈ H := by
  refine ⟨Subgroup.closure (s : Set Q), hLF s, ?_⟩
  intro q hq
  exact Subgroup.subset_closure hq

/-- In particular each finite tuple of elements of a locally
finite group belongs to a COMMON finite subgroup. -/
theorem locallyFinite_twoElements_finiteSubgroup
    (hLF : EveryFinitelyGeneratedSubgroupFinite Q)
    (a b : Q) :
    ∃ H : Subgroup Q, Finite H ∧ a ∈ H ∧ b ∈ H := by
  classical
  obtain ⟨H, hH, hCover⟩ :=
    locallyFinite_exists_finiteSubgroup_covering hLF ({a, b} : Finset Q)
  exact ⟨H, hH, hCover a (by simp),
    hCover b (by simp)⟩

end SemigenericEPPA
