import SemigenericEPPA.Algebra.CoherentPaddingSize
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.GroupTheory.Perm.Basic

/-!
# Extending a finite group action to a prechosen factorial-size fibre

The positive coherent-EPPA construction uses a *single* padding size
M=|A|! before the later induced substructure D and its group H
are selected. An occupied part of D is a nonempty subset S of A.

Once S embeds into a fibre of size M and H acts on S, that action
extends HOMOMORPHICALLY to a permutation action on the SAME padded
fibre, fixing one multiplicity coordinate:
  (s,r) -> (h s,r).

The proof first uses the divisibility |S| | M to choose a factor t
and a bijection Fin M ≃ S × Fin t. Its distinguished slice need
not equal the given old embedding j:S→Fin M. A finite extension
of injections supplies an ambient permutation aligning that slice
with j, so conjugating the product action preserves j EXACTLY.

Crucially the padded *carrier* Fin M is chosen before H, S and j.
Only its action depends on this later data. This is the cardinality
and strict-action gate needed in both coherent-positive sectors.
-/

namespace SemigenericEPPA

universe u v

/-- Any group action on a nonempty subset S of a fixed finite A
extends to an action on the PRECHOSEN padded fibre Fin(|A|!),
through ANY specified injection of S into that fibre.
The witness fibre type is independent of H and S. -/
theorem exists_factorialFibreGroupAction
    {A : Type u} [Fintype A]
    (S : Finset A) (hS : S.Nonempty)
    (j : S → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    {H : Type v} [Group H]
    (rho : H →* Equiv.Perm S) :
    ∃ lift : H →* Equiv.Perm (Fin (coherentPaddingSize A)),
      ∀ (h : H) (x : S),
        lift h (j x) = j (rho h x) := by
  classical
  obtain ⟨t, ht⟩ := exists_coherentPaddingMultiplicity S hS
  have htpos : 0 < t := by
    have hne : t ≠ 0 := by
      intro ht0
      have hzero : coherentPaddingSize A = 0 := by
        simpa [ht0] using ht.symm
      exact (Nat.ne_of_gt (coherentPaddingSize_pos A)) hzero
    exact Nat.pos_of_ne_zero hne
  letI : Fintype S := Finset.fintypeCoeSort S
  let z : Fin t := ⟨0, htpos⟩
  have hcard :
      Fintype.card (Fin (coherentPaddingSize A)) =
        Fintype.card (S × Fin t) := by
    simpa [Fintype.card_prod, Fintype.card_coe] using ht.symm
  let beta : Fin (coherentPaddingSize A) ≃ (S × Fin t) :=
    Fintype.equivOfCardEq hcard
  let j0 : S → Fin (coherentPaddingSize A) :=
    fun x => beta.symm (x,z)
  have hj0 : Function.Injective j0 := by
    intro x y hxy
    have hxy' : ((x,z) : S × Fin t) = (y,z) :=
      beta.symm.injective hxy
    exact congrArg Prod.fst hxy'
  obtain ⟨perm, hperm⟩ :=
    Equiv.Perm.exists_extending_pair j0 j hj0 hj
  let beta' : Fin (coherentPaddingSize A) ≃ (S × Fin t) :=
    perm.symm.trans beta
  have hbeta (x : S) : beta' (j x) = (x,z) := by
    have hx : perm.symm (j x) = j0 x := by
      rw [← hperm x]
      exact perm.symm_apply_apply (j0 x)
    calc
      beta' (j x) = beta (perm.symm (j x)) := rfl
      _ = beta (j0 x) := congrArg beta hx
      _ = (x,z) := beta.apply_symm_apply (x,z)
  let action : H →* Equiv.Perm (Fin (coherentPaddingSize A)) := {
    toFun := fun h =>
      (beta'.trans
        (Equiv.prodCongr (rho h) (Equiv.refl (Fin t)))).trans beta'.symm
    map_one' := by
      apply Equiv.ext
      intro x
      simp
    map_mul' := by
      intro k h
      apply Equiv.ext
      intro x
      simp [map_mul, Prod.map, Function.comp_def]
  }
  refine ⟨action, ?_⟩
  intro h x
  have hz : beta' (j (rho h x)) = (rho h x,z) :=
    hbeta (rho h x)
  calc
    action h (j x) =
        beta'.symm (rho h x,z) := by
          change beta'.symm
            ((Equiv.prodCongr (rho h) (Equiv.refl (Fin t)))
              (beta' (j x))) = beta'.symm (rho h x,z)
          rw [hbeta x]
          rfl
    _ = beta'.symm (beta' (j (rho h x))) := by rw [hz]
    _ = j (rho h x) := beta'.symm_apply_apply _

end SemigenericEPPA
