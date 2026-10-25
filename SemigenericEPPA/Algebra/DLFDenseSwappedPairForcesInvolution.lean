import SemigenericEPPA.Algebra.DLFLocallyFiniteFiniteContainer
import SemigenericEPPA.Algebra.DLFDirectedPermUnionDensity
import SemigenericEPPA.Algebra.DLFPairSwapEvenGroup

/-!
# Density + local finiteness + a two-cycle forces a genuine involution

This is the abstract final parity contradiction for negative DLF.

Suppose L≤A≤Perm(V) is dense on finite restrictions and locally finite.
If A contains an automorphism a swapping DISTINCT vertices x,y in
both directions, density gives a k∈L with the same exact two-cycle
on {x,y}. The element k need NOT be an involution: it could have order
4, 8, or an unrelated even order.

Local finiteness puts k inside ONE ACTUAL finite subgroup H≤L.
The certified finite-group parity lemma, applied to H's actual
permutation action, produces a nonidentity involution t∈H≤L.

Thus the negative semigeneric theorem reduces to showing that
a homogeneous full-age rectangle limit with no complete good
congruence orbit has NO nontrivial global involutions. That
geometric step needs the already certified raw delta/orbit-killer
obstructions and genuine Fraïssé extension property.
-/

namespace SemigenericEPPA

universe u
variable {V : Type u}

/-- A dense locally finite subgroup of any permutation group A
containing a literal two-cycle contains some GENUINE nonidentity
involution, not necessarily the approximating element itself. -/
theorem denseLocallyFinite_has_nontrivial_involution_of_swappedPair
    (A L : Subgroup (Equiv.Perm V))
    (hDense : DenseByFiniteRestrictions A L)
    (hLF : EveryFinitelyGeneratedSubgroupFinite L)
    (a : A) (x y : V)
    (hxy : a.val x = y) (hyx : a.val y = x)
    (hne : x ≠ y) :
    ∃ t : L, t ≠ 1 ∧ t * t = 1 := by
  classical
  obtain ⟨k, hk⟩ := hDense.2 a ({x, y} : Finset V)
  have hkxy : k.val x = y := (hk x (by simp)).trans hxy
  have hkyx : k.val y = x := (hk y (by simp)).trans hyx
  obtain ⟨H, hFinite, hContains⟩ :=
    locallyFinite_exists_finiteSubgroup_covering
      hLF ({k} : Finset L)
  letI : Finite H := hFinite
  have hkH : k ∈ H := hContains k (by simp)
  let rho : H →* Equiv.Perm V :=
    L.subtype.comp H.subtype
  have hxyH : rho ⟨k, hkH⟩ x = y := hkxy
  have hyxH : rho ⟨k, hkH⟩ y = x := hkyx
  obtain ⟨t, htne, htinv⟩ :=
    exists_nontrivial_involution_of_swappedPair
      rho ⟨k, hkH⟩ x y hxyH hyxH hne
  refine ⟨t.val, ?_, ?_⟩
  · intro hOne
    apply htne
    apply Subtype.ext
    exact hOne
  · exact congrArg Subtype.val htinv

end SemigenericEPPA
