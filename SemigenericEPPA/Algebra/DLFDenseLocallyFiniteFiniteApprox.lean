import SemigenericEPPA.Algebra.DLFLocallyFiniteFiniteContainer
import SemigenericEPPA.Algebra.DLFDirectedPermUnionDensity

/-!
# Dense locally finite permutation subgroups give finite approximation groups

The negative DLF argument cannot simply assume that a partial
involution extends to an actual involution. A dense subgroup of a
permutation group approximates a target automorphism on a chosen
finite set, but the approximating element may have larger order.

Local finiteness nevertheless puts that chosen approximant inside
a FINITE ACTUAL subgroup of the dense subgroup. This theorem
isolates the correct order of quantifiers:

* choose a target automorphism a and a finite set F;
* use density to select k in the ONE dense locally finite subgroup;
* choose an ACTUAL finite subgroup H containing k;
* k, as an element of H, still agrees with a on every vertex of F.

No assumption that a has finite order, that k has order two, or
that k preserves the originally selected finite set is made.
-/

namespace SemigenericEPPA

universe u
variable {V : Type u}

/-- Finite-group approximation on any finite vertex set from an
actual dense locally finite subgroup of permutations. -/
theorem denseLocallyFinite_exists_finiteSubgroup_approx
    (A L : Subgroup (Equiv.Perm V))
    (hDense : DenseByFiniteRestrictions A L)
    (hLF : EveryFinitelyGeneratedSubgroupFinite L)
    (a : A) (F : Finset V) :
    ∃ H : Subgroup L,
      Finite H ∧
      ∃ k : H, ∀ x : V, x ∈ F → k.val.val x = a.val x := by
  classical
  obtain ⟨k, hk⟩ := hDense.2 a F
  obtain ⟨H, hFinite, hContains⟩ :=
    locallyFinite_exists_finiteSubgroup_covering
      hLF ({k} : Finset L)
  have hkH : k ∈ H :=
    hContains k (by simp)
  refine ⟨H, hFinite, ⟨k, hkH⟩, ?_⟩
  exact hk

end SemigenericEPPA
