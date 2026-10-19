import SemigenericEPPA.Structure.EffectiveGeometry
import Mathlib.Algebra.Group.End

/-!
# Homomorphic class-index actions induced from a selected substructure

An H-action on a subset S of an E-geometry that preserves and reflects
E induces a strict H-action on the set of E-classes meeting S.
The action on the remaining classes can be taken to be the identity.
Unlike extending the H-action on S by the identity to all old vertices,
this induced quotient action moves the ENTIRE original class index:
vertices outside S within an occupied class cause no obstruction.

The two extensions are independently homomorphic and agree on the
original selected vertices.  This supplies the combinatorial group
actions required by the fixed-witness G=1 positive coherent sector.
No preservation of the original global E-relation by the extended
old-label action is asserted.
-/

namespace SemigenericEPPA

universe u v w
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- An H-action on S preserving the restricted E-equivalence extends
to an H-action on ALL original E-class indices, acting trivially on
classes that do not meet S. The action and its extension are strict
group homomorphisms, not independently chosen permutations. -/
theorem exists_occupiedQuotientGroupAction
    (D : EffectiveGeometry s V)
    (S : Set V)
    (rho : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      D.part x.val y.val ↔
        D.part (rho h x).val (rho h y).val) :
    ∃ iota : H →* Equiv.Perm (Quotient D.part),
      ∀ (h : H) (x : S),
        iota h (Quotient.mk D.part x.val) =
          Quotient.mk D.part (rho h x).val := by
  classical
  let f : S → Quotient D.part :=
    fun x => Quotient.mk D.part x.val
  let occupied : Set (Quotient D.part) := Set.range f
  let incl : S → occupied :=
    fun x => ⟨f x, ⟨x, rfl⟩⟩
  have hpres (h : H) (x y : S) (hxy : f x = f y) :
      f (rho h x) = f (rho h y) := by
    apply Quotient.sound
    exact (hE h x y).mp (Quotient.exact hxy)
  let rep (q : occupied) : S := Classical.choose q.property
  have hrep (q : occupied) : f (rep q) = q.val :=
    Classical.choose_spec q.property
  let forward (h : H) (q : occupied) : occupied :=
    ⟨f (rho h (rep q)), ⟨rho h (rep q), rfl⟩⟩
  have hforward (h : H) (x : S) :
      forward h (incl x) = incl (rho h x) := by
    apply Subtype.ext
    change f (rho h (rep (incl x))) = f (rho h x)
    exact hpres h (rep (incl x)) x (hrep (incl x))
  have hone (q : occupied) : forward (1 : H) q = q := by
    apply Subtype.ext
    change f (rho (1 : H) (rep q)) = q.val
    simpa using hrep q
  have hmul (k h : H) (q : occupied) :
      forward (k * h) q = forward k (forward h q) := by
    calc
      forward (k * h) q = incl (rho (k * h) (rep q)) := rfl
      _ = incl (rho k (rho h (rep q))) := by rw [map_mul]; rfl
      _ = forward k (incl (rho h (rep q))) :=
        (hforward k (rho h (rep q))).symm
      _ = forward k (forward h q) := rfl
  let perm (h : H) : Equiv.Perm occupied := {
    toFun := forward h
    invFun := forward h⁻¹
    left_inv := by
      intro q
      rw [← hmul (h⁻¹) h q, inv_mul_cancel]
      exact hone q
    right_inv := by
      intro q
      rw [← hmul h (h⁻¹) q, mul_inv_cancel]
      exact hone q
  }
  let occupiedAction : H →* Equiv.Perm occupied := {
    toFun := perm
    map_one' := by
      apply Equiv.ext
      intro q
      exact hone q
    map_mul' := by
      intro k h
      apply Equiv.ext
      intro q
      exact hmul k h q
  }
  let iota : H →* Equiv.Perm (Quotient D.part) :=
    (Equiv.Perm.ofSubtype
      (p := fun q : Quotient D.part => q ∈ occupied)).comp occupiedAction
  refine ⟨iota, ?_⟩
  intro h x
  change Equiv.Perm.ofSubtype (perm h) (f x) = f (rho h x)
  calc
    Equiv.Perm.ofSubtype (perm h) (f x) =
        (perm h (incl x)).val :=
      Equiv.Perm.ofSubtype_apply_coe (perm h) (incl x)
    _ = (incl (rho h x)).val :=
      congrArg Subtype.val (hforward h x)
    _ = f (rho h x) := rfl

/-- The real-label action has a strict extension by fixing the
complement of the selected subset. Combining it with the quotient
action above gives compatible homomorphic data for uniform padding.
This does NOT assert that the real-label extension preserves E on
all original V: it need not when S cuts through old E-classes. -/
theorem exists_compatibleSubsetAndQuotientActions
    (D : EffectiveGeometry s V)
    (S : Set V)
    (rho : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      D.part x.val y.val ↔
        D.part (rho h x).val (rho h y).val) :
    ∃ (tau : H →* Equiv.Perm V)
      (iota : H →* Equiv.Perm (Quotient D.part)),
      (∀ (h : H) (x : S),
        tau h x.val = (rho h x).val) ∧
      (∀ (h : H) (x : S),
        iota h (Quotient.mk D.part x.val) =
          Quotient.mk D.part (rho h x).val) := by
  classical
  obtain ⟨iota, hiota⟩ :=
    D.exists_occupiedQuotientGroupAction S rho hE
  let tau : H →* Equiv.Perm V :=
    (Equiv.Perm.ofSubtype (p := fun x : V => x ∈ S)).comp rho
  refine ⟨tau, iota, ?_, hiota⟩
  intro h x
  change Equiv.Perm.ofSubtype (rho h) x.val = (rho h x).val
  exact Equiv.Perm.ofSubtype_apply_coe (rho h) x

end EffectiveGeometry

end SemigenericEPPA
