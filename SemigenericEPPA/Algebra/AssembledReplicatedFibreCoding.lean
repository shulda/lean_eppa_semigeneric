import SemigenericEPPA.Algebra.FixedFibreSliceCoding
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Assemble classwise fixed-fibre codings into one occupied bundle

For an arbitrary later selected finite old vertex set S and its
E-class label cls:S→I, consider the fixed carrier I×Fin M.  Only
classes meeting S are occupied.  A fibrewise equivalence
    β_i : Fin M ≃ {x:S | cls x=i} × Fin(t_i)
can be assembled to a SINGLE equivalence between the occupied
portion of the fixed carrier and the true replica bundle
    Σ x:S, Fin(t_(cls x)).

This is the missing type-level assembly between the strict
replicated group action and the fixed fibre coding. Importantly
the original padded carrier I×Fin M does NOT depend on S or H.
-/

namespace SemigenericEPPA

universe u v

variable {S : Type u} {I : Type v}

/-- E-class indices actually visited by S. -/
abbrev ReplicatedOccupiedIndex (cls : S → I) :=
  {i : I // ∃ x : S, cls x = i}

/-- Old vertices belonging to one occupied part. -/
abbrev ReplicatedOldFibre
    (cls : S → I)
    (i : ReplicatedOccupiedIndex cls) :=
  {x : S // cls x = i.val}

/-- The occupied portion of the fixed global carrier I×Fin M. -/
abbrev ReplicatedOccupiedCarrier
    (cls : S → I) (M : ℕ) :=
  {z : I × Fin M // ∃ x : S, cls x = z.1}

/-- Separate an occupied fixed carrier vertex into its actual
occupied class index and its still-fixed fibre coordinate. -/
def replicatedOccupiedPairEquiv
    (cls : S → I) (M : ℕ) :
    ReplicatedOccupiedCarrier cls M ≃
      (Σ i : ReplicatedOccupiedIndex cls, Fin M) where
  toFun := fun z => ⟨⟨z.val.1, z.property⟩, z.val.2⟩
  invFun := fun z => ⟨(z.1.val, z.2), z.1.property⟩
  left_inv := by
    rintro ⟨⟨i,u⟩,hi⟩
    rfl
  right_inv := by
    rintro ⟨⟨i,hi⟩,u⟩
    rfl

/-- Re-associate the indexed fibres into the canonical replica
bundle, retaining all dependent multiplicity indices literally. -/
def replicatedSigmaReassociate
    (cls : S → I) (t : I → ℕ) :
    (Σ i : ReplicatedOccupiedIndex cls,
      ReplicatedOldFibre cls i × Fin (t i.val)) ≃
    (Σ x : S, Fin (t (cls x))) where
  toFun := fun z =>
    ⟨z.2.1.val, ⟨z.2.2.val, by
      rw [z.2.1.property]
      exact z.2.2.isLt⟩⟩
  invFun := fun z =>
    ⟨⟨cls z.1, ⟨z.1,rfl⟩⟩, (⟨z.1,rfl⟩, z.2)⟩
  left_inv := by
    rintro ⟨⟨i,hi⟩, ⟨⟨x,hx⟩,r⟩⟩
    dsimp
    cases hx
    rfl
  right_inv := by
    rintro ⟨x,r⟩
    rfl

/-- Assemble ALL individual fibre identifications β_i into one
genuine equivalence from the occupied part of the same fixed
carrier I×Fin M to the entire replicated old-label bundle. -/
noncomputable def assembledReplicatedFibreEquiv
    (cls : S → I) (t : I → ℕ) (M : ℕ)
    (beta : ∀ i : ReplicatedOccupiedIndex cls,
      Fin M ≃ ReplicatedOldFibre cls i × Fin (t i.val)) :
    ReplicatedOccupiedCarrier cls M ≃
      (Σ x : S, Fin (t (cls x))) :=
  ((replicatedOccupiedPairEquiv cls M).trans
    (Equiv.sigmaCongrRight beta)).trans
      (replicatedSigmaReassociate cls t)

/-- The assembled coding preserves class indices exactly, not
merely the partition or a cardinality bound. -/
theorem assembledReplicatedFibreEquiv_class
    (cls : S → I) (t : I → ℕ) (M : ℕ)
    (beta : ∀ i : ReplicatedOccupiedIndex cls,
      Fin M ≃ ReplicatedOldFibre cls i × Fin (t i.val))
    (z : ReplicatedOccupiedCarrier cls M) :
    cls (assembledReplicatedFibreEquiv cls t M beta z).1 =
      z.val.1 := by
  change cls
      (replicatedSigmaReassociate cls t
        ⟨⟨z.val.1,z.property⟩,
          beta ⟨z.val.1,z.property⟩ z.val.2⟩).1 =
        z.val.1
  exact (beta ⟨z.val.1,z.property⟩ z.val.2).1.property

/-- A β_i which sends all previously embedded old vertices to
(x,0) yields an assembled coding with EXACT old vertices in
the distinguished copy-zero slice. -/
theorem assembledReplicatedFibreEquiv_old
    (cls : S → I) (t : I → ℕ) (M : ℕ)
    (hpos : ∀ i : ReplicatedOccupiedIndex cls, 0 < t i.val)
    (j : ∀ i : ReplicatedOccupiedIndex cls,
      ReplicatedOldFibre cls i → Fin M)
    (beta : ∀ i : ReplicatedOccupiedIndex cls,
      Fin M ≃ ReplicatedOldFibre cls i × Fin (t i.val))
    (hbeta : ∀ (i : ReplicatedOccupiedIndex cls)
       (x : ReplicatedOldFibre cls i),
      beta i (j i x) = (x, (⟨0,hpos i⟩ : Fin (t i.val))))
    (x : S) :
    assembledReplicatedFibreEquiv cls t M beta
      ⟨(cls x, j ⟨cls x, ⟨x,rfl⟩⟩ ⟨x,rfl⟩),
        ⟨x,rfl⟩⟩ =
      ⟨x, (⟨0,hpos ⟨cls x, ⟨x,rfl⟩⟩⟩ :
        Fin (t (cls x)))⟩ := by
  change replicatedSigmaReassociate cls t
      ⟨⟨cls x,⟨x,rfl⟩⟩,
        beta ⟨cls x,⟨x,rfl⟩⟩
          (j ⟨cls x,⟨x,rfl⟩⟩ ⟨x,rfl⟩)⟩ = _
  rw [hbeta]
  rfl

end SemigenericEPPA
