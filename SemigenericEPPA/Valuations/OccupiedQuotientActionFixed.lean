import SemigenericEPPA.Valuations.OccupiedQuotientGroupAction

/-!
# The induced quotient action is pointwise trivial on unoccupied classes

The previous occupied-quotient construction chooses the action on
visited old E-classes and extends by identity outside its image.
Here the identity property is made explicit in the public theorem
signature; it is REQUIRED to rule out artificial swapped edges
crossing the unoccupied sector of the padded witness.

We retain the original less-constrained theorem for compatibility.
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
theorem exists_occupiedQuotientGroupAction_fixed
    (D : EffectiveGeometry s V)
    (S : Set V)
    (rho : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      D.part x.val y.val ↔
        D.part (rho h x).val (rho h y).val) :
    ∃ iota : H →* Equiv.Perm (Quotient D.part),
      (∀ (h : H) (x : S),
        iota h (Quotient.mk D.part x.val) =
          Quotient.mk D.part (rho h x).val) ∧
      (∀ (h : H) (i : Quotient D.part),
        (¬∃ x : S, Quotient.mk D.part x.val = i) →
          iota h i = i) := by
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
  refine ⟨iota, ?_, ?_⟩
  · intro h x
    change Equiv.Perm.ofSubtype (perm h) (f x) = f (rho h x)
    calc
      Equiv.Perm.ofSubtype (perm h) (f x) =
          (perm h (incl x)).val :=
        Equiv.Perm.ofSubtype_apply_coe (perm h) (incl x)
      _ = (incl (rho h x)).val :=
        congrArg Subtype.val (hforward h x)
      _ = f (rho h x) := rfl
  · intro h i hi
    change Equiv.Perm.ofSubtype (perm h) i = i
    exact Equiv.Perm.ofSubtype_apply_of_not_mem (perm h) hi


/-- A strict real-label and class-index action extending an H-action
on S, with the additional essential guarantee that every unoccupied
E-class index is fixed pointwise. -/
theorem exists_compatibleSubsetAndQuotientActions_fixed
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
          Quotient.mk D.part (rho h x).val) ∧
      (∀ (h : H) (i : Quotient D.part),
        (¬∃ x : S, Quotient.mk D.part x.val = i) →
          iota h i = i) := by
  classical
  obtain ⟨iota, hiota, hfix⟩ :=
    D.exists_occupiedQuotientGroupAction_fixed S rho hE
  let tau : H →* Equiv.Perm V :=
    (Equiv.Perm.ofSubtype (p := fun x : V => x ∈ S)).comp rho
  refine ⟨tau, iota, ?_, hiota, hfix⟩
  intro h x
  change Equiv.Perm.ofSubtype (rho h) x.val = (rho h x).val
  exact Equiv.Perm.ofSubtype_apply_coe (rho h) x

end EffectiveGeometry

end SemigenericEPPA
