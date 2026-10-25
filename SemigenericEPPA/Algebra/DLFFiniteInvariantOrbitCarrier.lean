import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin

/-!
# Every finite set lies in a finite invariant carrier for a finite permutation group

The negative DLF argument first extracts a genuinely finite subgroup
H of a dense locally finite automorphism group. The ambient homogeneous
structure is infinite, so an H-action must be restricted to a finite
H-invariant induced substructure before applying the finite raw
delta-profile and involution constraints.

For any finite permutation group H≤Perm V and finite set F⊆V,
its orbit closure H·F is finite and H-invariant. Unlike assuming
the old finite set F itself is invariant, this is always valid.

The resulting closed finite vertex set can be used as the carrier
of a pulled-back original-language rectangle. No assertion that
an arbitrary superstructure supports the same H-action is needed.
-/

namespace SemigenericEPPA

universe u
variable {V : Type u}

/-- The orbit closure of a finite subset under a finite subgroup
of the permutation group is an actual finite set. -/
noncomputable def finiteGroupOrbitFinset
    (H : Subgroup (Equiv.Perm V)) [Finite H] (F : Finset V) :
    Finset V := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  exact Finset.univ.biUnion (fun h : H => F.image h.val)

/-- A finite set is contained in its finite-group orbit closure. -/
theorem finiteGroupOrbitFinset_contains
    (H : Subgroup (Equiv.Perm V)) [Finite H]
    (F : Finset V) :
    F ⊆ finiteGroupOrbitFinset H F := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  intro x hx
  unfold finiteGroupOrbitFinset
  apply Finset.mem_biUnion.mpr
  refine ⟨(1 : H), Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨x, hx, ?_⟩
  simp

/-- The finite orbit closure is invariant under the ENTIRE original
finite permutation group, not only each chosen generator. -/
theorem finiteGroupOrbitFinset_invariant
    (H : Subgroup (Equiv.Perm V)) [Finite H]
    (F : Finset V) (h : H)
    (x : V) (hx : x ∈ finiteGroupOrbitFinset H F) :
    h.val x ∈ finiteGroupOrbitFinset H F := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  unfold finiteGroupOrbitFinset at hx ⊢
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨y, hy, hky⟩ := Finset.mem_image.mp hk
  refine Finset.mem_biUnion.mpr
    ⟨h * k, Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨y, hy, ?_⟩
  calc
    (h * k).val y = h.val (k.val y) := rfl
    _ = h.val x := congrArg h.val hky

end SemigenericEPPA
