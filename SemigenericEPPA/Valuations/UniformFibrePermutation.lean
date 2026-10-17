import SemigenericEPPA.Valuations.PartialPartPermutation

/-!
# Extension of old real-label maps on uniformly sized E-parts

After padding all old E-classes to the same cardinality, the real
vertices have an identification with I × U, where I is the old
part-imaginary sort and U is one common finite fibre.  A partial
injection whose part map agrees with an already chosen permutation
ι : I ≃ I extends to a *global* real-label permutation π satisfying
π(i,u).1 = ι(i) everywhere.

The fibre permutations are chosen independently by the finite
extension-of-injections lemma.  This is the point where uniform
fibre size is used in the manuscript's (3.13); without padding it is
generally false.  No preservation of effective colours or EPPA theorem
is assumed here.
-/

namespace SemigenericEPPA

universe u v

/-- A partial injection between points in uniform fibres, compatible
with a prescribed permutation of the imaginary sort, extends to an
actual permutation of all real labels.  In particular, an empty partial
domain causes no problem.  The number of parts need not itself be
finite: only the common fibre must be finite. -/
theorem exists_uniformFibrePermutation_extending
    {I : Type u} {U : Type v} [Finite U]
    (S : Set (I × U)) (p : S → I × U)
    (hp : Function.Injective p)
    (ι : Equiv.Perm I)
    (hι : ∀ x : S, (p x).1 = ι x.val.1) :
    ∃ π : Equiv.Perm (I × U),
      (∀ z : I × U, (π z).1 = ι z.1) ∧
      (∀ x : S, π x.val = p x) := by
  classical
  have h_local (i : I) :
      ∃ e : Equiv.Perm U,
        ∀ x : {u : U // (i,u) ∈ S},
          e x.val = (p ⟨(i,x.val), x.property⟩).2 := by
    let f : {u : U // (i,u) ∈ S} → U := Subtype.val
    let g : {u : U // (i,u) ∈ S} → U :=
      fun x => (p ⟨(i,x.val), x.property⟩).2
    have hf : Function.Injective f := Subtype.val_injective
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      have hpy :
          p ⟨(i,x.val), x.property⟩ =
            p ⟨(i,y.val), y.property⟩ := by
        apply Prod.ext
        · exact (hι ⟨(i,x.val), x.property⟩).trans
            (hι ⟨(i,y.val), y.property⟩).symm
        · exact hxy
      have hxy' := hp hpy
      exact congrArg (fun z : S => z.val.2) hxy'
    obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
    exact ⟨e, he⟩
  let ρ : I → Equiv.Perm U := fun i => Classical.choose (h_local i)
  have hρ (i : I) (x : {u : U // (i,u) ∈ S}) :
      ρ i x.val = (p ⟨(i,x.val), x.property⟩).2 :=
    (Classical.choose_spec (h_local i)) x
  let π : Equiv.Perm (I × U) := {
    toFun := fun z => (ι z.1, ρ z.1 z.2)
    invFun := fun z => (ι.symm z.1, (ρ (ι.symm z.1)).symm z.2)
    left_inv := by
      rintro ⟨i,u⟩
      apply Prod.ext
      · exact ι.symm_apply_apply i
      · change (ρ (ι.symm (ι i))).symm (ρ i u) = u
        rw [ι.symm_apply_apply]
        exact (ρ i).symm_apply_apply u
    right_inv := by
      rintro ⟨i,u⟩
      apply Prod.ext
      · exact ι.apply_symm_apply i
      · change ρ (ι.symm i) ((ρ (ι.symm i)).symm u) = u
        exact (ρ (ι.symm i)).apply_symm_apply u
  }
  refine ⟨π, ?_, ?_⟩
  · intro z
    rfl
  · intro x
    apply Prod.ext
    · change ι x.val.1 = (p x).1
      exact (hι x).symm
    · change ρ x.val.1 x.val.2 = (p x).2
      exact hρ x.val.1 ⟨x.val.2, x.property⟩

end SemigenericEPPA
