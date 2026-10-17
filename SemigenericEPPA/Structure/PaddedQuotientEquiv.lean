import SemigenericEPPA.Structure.UniformPadding

/-!
# Recover the literal E-part imaginary sort after uniform padding

The canonical quotient of the padded setoid on (V/E) × V is a new
Lean type, even though it is mathematically the original part-index
sort I=V/E.  The effective valuation witness indexes its parts by the
canonical *padded* quotient, not by I.

Here we give the actual equivalence
    ((V/E) × V)/E_padded ≃ V/E
including the empty-carrier case (representatives exist for each
inhabited quotient class). We then transport permutations of I into
permutations of the canonical padded imaginary sort and prove the
exact compatibility with any real-label permutation respecting I.

This is a type-level bridge for the (3.13) / (3.17) witness
construction, not an EPPA or effective-colour automorphism theorem.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

variable (D : EffectiveGeometry s V)

/-- Recover the original imaginary E-classes from the quotient of
the uniformly padded E relation.  The inverse selects any old
representative of a part to define a padded point. -/
noncomputable def paddedClassEquiv :
    Quotient D.uniformPaddedGeometry.part ≃ Quotient D.part where
  toFun := Quotient.lift (fun z : Quotient D.part × V => z.1) (by
    intro z w hzw
    exact (D.uniformPaddedGeometry_part z w).mp hzw)
  invFun := fun i =>
    Quotient.mk D.uniformPaddedGeometry.part (i, D.representative i)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ z =>
      apply Quotient.sound
      change z.1 = z.1
      rfl
  right_inv := by
    intro i
    rfl

@[simp] theorem paddedClassEquiv_class
    (z : Quotient D.part × V) :
    D.paddedClassEquiv (Quotient.mk D.uniformPaddedGeometry.part z) =
      z.1 := rfl

@[simp] theorem paddedClassEquiv_old
    (x : V) :
    D.paddedClassEquiv
        (Quotient.mk D.uniformPaddedGeometry.part (D.paddedOldMap x)) =
      Quotient.mk D.part x := rfl

/-- Conjugate a permutation of old imaginary parts to the canonical
imaginary sort of the padded geometry. -/
noncomputable def paddedPartPermutation
    (ι : Equiv.Perm (Quotient D.part)) :
    Equiv.Perm (Quotient D.uniformPaddedGeometry.part) :=
  (D.paddedClassEquiv.trans ι).trans D.paddedClassEquiv.symm

/-- The conjugate permutation of padded E-classes is compatible with
every real-label permutation whose first coordinate follows ι.
This is the precise condition required by twistedWitnessFibreEquiv. -/
theorem paddedPartPermutation_class
    (ι : Equiv.Perm (Quotient D.part))
    (π : Equiv.Perm (Quotient D.part × V))
    (hπ : ∀ z : Quotient D.part × V, (π z).1 = ι z.1)
    (z : Quotient D.part × V) :
    D.paddedPartPermutation ι
        (Quotient.mk D.uniformPaddedGeometry.part z) =
      Quotient.mk D.uniformPaddedGeometry.part (π z) := by
  apply D.paddedClassEquiv.injective
  calc
    D.paddedClassEquiv
        (D.paddedPartPermutation ι
          (Quotient.mk D.uniformPaddedGeometry.part z)) =
      ι z.1 := by
        simp [paddedPartPermutation]
    _ = (π z).1 := (hπ z).symm
    _ = D.paddedClassEquiv
          (Quotient.mk D.uniformPaddedGeometry.part (π z)) := by
        rw [D.paddedClassEquiv_class]

end EffectiveGeometry

end SemigenericEPPA
