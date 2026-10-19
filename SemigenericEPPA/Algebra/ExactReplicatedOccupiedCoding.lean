import SemigenericEPPA.Algebra.ExistAssembledReplicatedCoding
import SemigenericEPPA.Valuations.ReplicatedFibreLabelAction

/-!
# One fixed-carrier replica coding with certified class and old coordinates

For each occupied index i, choose a bijection of the prechosen
fibre Fin M with actual old fibre X_i × Fin(t_i), whose copy-zero
slice coincides with the prescribed old injection j_i. This exists
from finiteness, positivity, and exact cardinality alone.

The resulting *single* coding e : replicated old bundle ≃ occupied
part of I×Fin M has both crucial, literal properties:

* Its image has the correct E-part index cls(x) for EVERY copy (x,r).
* It sends the old copy-zero label (x,0) to the old fixed embedding
  (cls(x), j_{cls(x)}(x)) EXACTLY.

Unlike the older existence statement, the class preservation is
returned as a theorem hypothesis usable by the group action and
flip-safety bridges; no arbitrary β_i is required from consumers.
-/

namespace SemigenericEPPA

universe u v

variable {S : Type u} {I : Type v}

theorem exists_exactReplicatedOccupiedCoding
    (cls : S → I) (t : I → ℕ) (M : ℕ)
    (hfin : ∀ i : ReplicatedOccupiedIndex cls,
      Fintype (ReplicatedOldFibre cls i))
    (hpos : ∀ i : ReplicatedOccupiedIndex cls, 0 < t i.val)
    (hsize : ∀ i : ReplicatedOccupiedIndex cls,
      (@Fintype.card (ReplicatedOldFibre cls i) (hfin i)) *
        t i.val = M)
    (j : ∀ i : ReplicatedOccupiedIndex cls,
      ReplicatedOldFibre cls i → Fin M)
    (hj : ∀ i : ReplicatedOccupiedIndex cls,
      Function.Injective (j i)) :
    ∃ e : ReplicatedFibreLabel cls t ≃
        ReplicatedOccupiedCarrier cls M,
      (∀ z : ReplicatedFibreLabel cls t,
        (e z).val.1 = cls z.1) ∧
      (∀ x : S,
        (e (replicatedFibreOldLabel cls t
          (fun y => hpos ⟨cls y,⟨y,rfl⟩⟩) x)).val =
          (cls x, j ⟨cls x,⟨x,rfl⟩⟩ ⟨x,rfl⟩)) := by
  classical
  obtain ⟨beta, hbeta⟩ :=
    exists_fixedFibreSliceCoding_family
      (X := fun i : ReplicatedOccupiedIndex cls =>
        ReplicatedOldFibre cls i)
      hfin M (fun i => t i.val) hpos hsize j hj
  let u : ReplicatedOccupiedCarrier cls M ≃
      ReplicatedFibreLabel cls t :=
    assembledReplicatedFibreEquiv cls t M beta
  let e : ReplicatedFibreLabel cls t ≃
      ReplicatedOccupiedCarrier cls M := u.symm
  refine ⟨e, ?_, ?_⟩
  · intro z
    have hz : cls ((u (u.symm z)).1) = (u.symm z).val.1 :=
      assembledReplicatedFibreEquiv_class cls t M beta (u.symm z)
    rw [u.apply_symm_apply] at hz
    exact hz.symm
  · intro x
    have hold := assembledReplicatedFibreEquiv_old
      cls t M hpos j beta hbeta x
    have hold' : u
        ⟨(cls x, j ⟨cls x,⟨x,rfl⟩⟩ ⟨x,rfl⟩),⟨x,rfl⟩⟩ =
        replicatedFibreOldLabel cls t
          (fun y => hpos ⟨cls y,⟨y,rfl⟩⟩) x := by
      simpa only [replicatedFibreOldLabel] using hold
    have heq :
        e (replicatedFibreOldLabel cls t
          (fun y => hpos ⟨cls y,⟨y,rfl⟩⟩) x) =
        (⟨(cls x,j ⟨cls x,⟨x,rfl⟩⟩ ⟨x,rfl⟩),⟨x,rfl⟩⟩ :
          ReplicatedOccupiedCarrier cls M) := by
      apply u.injective
      calc
        u (e (replicatedFibreOldLabel cls t
            (fun y => hpos ⟨cls y,⟨y,rfl⟩⟩) x)) =
            replicatedFibreOldLabel cls t
              (fun y => hpos ⟨cls y,⟨y,rfl⟩⟩) x :=
          u.apply_symm_apply _
        _ = u ⟨(cls x, j ⟨cls x,⟨x,rfl⟩⟩ ⟨x,rfl⟩),⟨x,rfl⟩⟩ :=
          hold'.symm
    exact congrArg Subtype.val heq

end SemigenericEPPA
