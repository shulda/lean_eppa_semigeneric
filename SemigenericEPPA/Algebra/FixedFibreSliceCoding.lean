import SemigenericEPPA.Algebra.FactorialFibreGroupAction
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Logic.Equiv.Fintype

/-!
# Replicated-fibre coding on a prechosen fixed carrier

An occupied E-class of a later induced old substructure has a
nonempty set X of genuine old vertices.  The globally fixed padded
fibre has M points, where |X| divides M.  A chosen injection j:X→Fin M
specifies the ORIGINAL embedding, which must not move after the later
substructure and its automorphism group have been selected.

The present lemma builds an honest bijection
    β : Fin M ≃ X × Fin t,        |X| * t = M,
that maps every j(x) EXACTLY to (x,0).  Therefore its inverse
identifies the entire fixed fibre with t genuine copies of X, the
zero copy being the original old embedding.

No permutation action is chosen here.  Once β_i is available for
every occupied E-class, the strict H-action on the replicated copies
can be transported by conjugation (its composition law is supplied
by ReplicatedFibreLabelAction).
-/

namespace SemigenericEPPA

universe u v

/-- A single fixed finite carrier can be coded by equally many
copies of X while preserving ANY previously chosen injection
j:X↪Fin M as the copy-zero slice. -/
theorem exists_fixedFibreSliceCoding
    {X : Type u} [Fintype X]
    (M t : ℕ)
    (htpos : 0 < t)
    (ht : Fintype.card X * t = M)
    (j : X → Fin M)
    (hj : Function.Injective j) :
    ∃ beta : Fin M ≃ X × Fin t,
      ∀ x : X, beta (j x) = (x, (⟨0, htpos⟩ : Fin t)) := by
  classical
  let z : Fin t := ⟨0, htpos⟩
  have hcard :
      Fintype.card (Fin M) = Fintype.card (X × Fin t) := by
    simpa [Fintype.card_prod] using ht.symm
  let beta₀ : Fin M ≃ X × Fin t :=
    Fintype.equivOfCardEq hcard
  let j₀ : X → Fin M := fun x => beta₀.symm (x, z)
  have hj₀ : Function.Injective j₀ := by
    intro x y hxy
    have hxy' : ((x,z) : X × Fin t) = (y,z) :=
      beta₀.symm.injective hxy
    exact congrArg Prod.fst hxy'
  obtain ⟨perm, hperm⟩ :=
    Equiv.Perm.exists_extending_pair j₀ j hj₀ hj
  let beta : Fin M ≃ X × Fin t := perm.symm.trans beta₀
  refine ⟨beta, ?_⟩
  intro x
  have hx : perm.symm (j x) = j₀ x := by
    rw [← hperm x]
    exact perm.symm_apply_apply (j₀ x)
  calc
    beta (j x) = beta₀ (perm.symm (j x)) := rfl
    _ = beta₀ (j₀ x) := congrArg beta₀ hx
    _ = (x,z) := beta₀.apply_symm_apply (x,z)

/-- Uniformly choose all required classwise identifications at once.
The COMMON ambient carrier Fin M is fixed before the family of
fibre types X_i, the later induced subset, or any group H.
Different parts can have different multiplicities t_i. -/
theorem exists_fixedFibreSliceCoding_family
    {I : Type v} (X : I → Type u)
    (hfin : ∀ i : I, Fintype (X i))
    (M : ℕ)
    (t : I → ℕ)
    (htpos : ∀ i : I, 0 < t i)
    (ht : ∀ i : I, (@Fintype.card (X i) (hfin i)) * t i = M)
    (j : ∀ i : I, X i → Fin M)
    (hj : ∀ i : I, Function.Injective (j i)) :
    ∃ beta : ∀ i : I, Fin M ≃ X i × Fin (t i),
      ∀ (i : I) (x : X i),
        beta i (j i x) =
          (x, (⟨0, htpos i⟩ : Fin (t i))) := by
  classical
  have hlocal (i : I) :
      ∃ beta : Fin M ≃ X i × Fin (t i),
        ∀ x : X i, beta (j i x) =
          (x, (⟨0, htpos i⟩ : Fin (t i))) := by
    letI : Fintype (X i) := hfin i
    exact exists_fixedFibreSliceCoding M (t i)
      (htpos i) (ht i) (j i) (hj i)
  let beta (i : I) : Fin M ≃ X i × Fin (t i) :=
    Classical.choose (hlocal i)
  refine ⟨beta, ?_⟩
  intro i x
  exact (Classical.choose_spec (hlocal i)) x

end SemigenericEPPA
