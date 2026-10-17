import SemigenericEPPA.Valuations.UniformFibrePermutation
import SemigenericEPPA.Structure.UniformPadding

/-!
# The full E-class and real-label permutation step (3.13)

This closes the permutation argument in the effective EPPA proof.
For *any* partial injection p on a finite old effective geometry that
preserves and reflects E, first extend its map on the old E-class
imaginaries to ι, then use the explicit uniform padding
(V/E) × V to extend p to an actual permutation π of all padded real
labels. The permutation π globally preserves/refects E, and follows
ι on every E-class.

Crucially, π is not asserted to preserve group-valued cross-colours:
that additional automorphism is built only later, using valuation
twists and prescribed gauge multipliers (3.14)--(3.19). The present
result is a genuine unconditional lift of the partial *E*-map on
the padded carrier, with no equal-size hypothesis on old classes.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- An arbitrary partial injection preserving/reflection E lifts,
after the verified uniform padding, to an E-preserving permutation
of *all* padded real labels that extends the old partial map literally.
The associated permutation ι of the old part-index sort is returned
together with π, satisfying (3.13) on all padded vertices. -/
theorem exists_paddedPartAndRealPermutations
    [Finite V] (D : EffectiveGeometry s V)
    (S : Set V) (p : S → V)
    (hp : Function.Injective p)
    (hE : ∀ x y : S, D.part x.val y.val ↔ D.part (p x) (p y)) :
    ∃ (ι : Equiv.Perm (Quotient D.part))
      (π : Equiv.Perm (Quotient D.part × V)),
      (∀ z : Quotient D.part × V, (π z).1 = ι z.1) ∧
      (∀ z w : Quotient D.part × V,
        D.uniformPaddedGeometry.part (π z) (π w) ↔
          D.uniformPaddedGeometry.part z w) ∧
      (∀ x : S, π (D.paddedOldMap x.val) = D.paddedOldMap (p x)) := by
  classical
  obtain ⟨ι, hι⟩ := D.exists_partPermutation_extending S p hE
  -- This subtype is the literal image of the original partial domain
  -- under the old embedding x ↦ ([x],x); no inverse choice is needed.
  let T : Set (Quotient D.part × V) :=
    { z | z.1 = Quotient.mk D.part z.2 ∧ z.2 ∈ S }
  let pp : T → Quotient D.part × V := fun z =>
    D.paddedOldMap (p ⟨z.val.2, z.property.2⟩)
  have hpp : Function.Injective pp := by
    intro x y hxy
    have hreal :
        p ⟨x.val.2, x.property.2⟩ =
          p ⟨y.val.2, y.property.2⟩ :=
      D.paddedOldMap_injective hxy
    have hsecond : x.val.2 = y.val.2 :=
      congrArg Subtype.val (hp hreal)
    apply Subtype.ext
    apply Prod.ext
    · calc
        x.val.1 = Quotient.mk D.part x.val.2 := x.property.1
        _ = Quotient.mk D.part y.val.2 :=
          congrArg (Quotient.mk D.part) hsecond
        _ = y.val.1 := y.property.1.symm
    · exact hsecond
  have hppart : ∀ z : T, (pp z).1 = ι z.val.1 := by
    intro z
    change Quotient.mk D.part (p ⟨z.val.2, z.property.2⟩) = ι z.val.1
    calc
      Quotient.mk D.part (p ⟨z.val.2, z.property.2⟩) =
          ι (Quotient.mk D.part z.val.2) :=
        (hι ⟨z.val.2, z.property.2⟩).symm
      _ = ι z.val.1 := congrArg ι z.property.1.symm
  obtain ⟨π, hπpart, hπext⟩ :=
    exists_uniformFibrePermutation_extending T pp hpp ι hppart
  refine ⟨ι, π, hπpart, ?_, ?_⟩
  · intro z w
    change (π z).1 = (π w).1 ↔ z.1 = w.1
    rw [hπpart z, hπpart w]
    constructor
    · intro h
      exact ι.injective h
    · intro h
      exact congrArg ι h
  · intro x
    let z : T := ⟨D.paddedOldMap x.val, ⟨rfl, x.property⟩⟩
    have hz := hπext z
    change π (D.paddedOldMap x.val) = D.paddedOldMap (p x) at hz
    exact hz

end EffectiveGeometry

end SemigenericEPPA
