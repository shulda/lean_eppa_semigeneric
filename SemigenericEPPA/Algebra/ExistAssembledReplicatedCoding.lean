import SemigenericEPPA.Algebra.AssembledReplicatedFibreCoding

/-!
# Existence of one occupied replica coding on a prechosen carrier

The classwise β_i codings need not be supplied by the caller.
Given only finite actual old fibres X_i, multiplicities t_i with
|X_i|*t_i=M, and prescribed injective old maps j_i:X_i↪Fin M,
the already verified family coding theorem produces all β_i
SIMULTANEOUSLY. The assembled equivalence then identifies the
occupied part of I×Fin M with the canonical old-replica bundle.

The carrier I×Fin M is chosen before these inputs; the chosen coding
depends on the later selected old subset (as it is allowed to).
-/

namespace SemigenericEPPA

universe u v

variable {S : Type u} {I : Type v}

/-- Produce the full occupied class coding with the exact old
copy-zero embeddings. Unlike the raw family assembly, this statement
assumes no arbitrary β_i equivalences: only divisibility/cardinality
and injectivity, with the same prechosen M in every part. -/
theorem exists_assembledReplicatedFibreCoding
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
    ∃ e : ReplicatedOccupiedCarrier cls M ≃
        (Σ x : S, Fin (t (cls x))),
      ∀ x : S,
        e ⟨(cls x,
          j ⟨cls x, ⟨x,rfl⟩⟩ ⟨x,rfl⟩),
            ⟨x,rfl⟩⟩ =
          ⟨x, (⟨0,hpos ⟨cls x,⟨x,rfl⟩⟩⟩ :
            Fin (t (cls x)))⟩ := by
  classical
  obtain ⟨beta, hbeta⟩ :=
    exists_fixedFibreSliceCoding_family
      (X := fun i : ReplicatedOccupiedIndex cls =>
        ReplicatedOldFibre cls i)
      hfin M (fun i => t i.val) hpos hsize j hj
  refine ⟨assembledReplicatedFibreEquiv cls t M beta, ?_⟩
  intro x
  exact assembledReplicatedFibreEquiv_old
    cls t M hpos j beta hbeta x

end SemigenericEPPA
