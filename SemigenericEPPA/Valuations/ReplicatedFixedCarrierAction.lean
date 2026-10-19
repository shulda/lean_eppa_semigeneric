import SemigenericEPPA.Valuations.ReplicatedFibreLabelAction
import Mathlib.Algebra.Group.End

/-!
# Strict replicated-fibre group actions on a prechosen fixed carrier

Suppose an occupied subset of an already fixed carrier W is
identified, by ONE chosen bijection e, with the replicated old
vertex type Σ x:S, Fin(t(class x)).  We conjugate the certified
strict H-action through e, then extend it by identity outside
the occupied subset.

This is the exact group-law and old-embedding transport needed
for the positive coherent EPPA construction.  Both the global
carrier W and the old injection are fixed; the coding e may be
chosen after the induced old substructure and H are given.
Unoccupied elements never move.

A separate geometric step must construct e from the fixed-fibre
slice codings β_i; nothing is assumed about the raw colouring yet.
-/

namespace SemigenericEPPA

universe u v w z

variable {H : Type u} [Group H]
variable {S : Type v} {I : Type w} {W : Type z}

/-- Transport the strict replicated-label action to a fixed global
carrier. All points outside the occupied subset stay fixed.
The proof uses a group-homomorphic subtype permutation extension
rather than choosing individual inverse permutations. -/
noncomputable def replicatedFixedCarrierGroupAction
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (t : I → ℕ)
    (ht : ∀ (h : H) (i : I),
      t (iota h i) = t i)
    (idx : W → I)
    (occupied : I → Prop)
    (e : ReplicatedFibreLabel cls t ≃
        {w : W // occupied (idx w)}) :
    H →* Equiv.Perm W := by
  classical
  let act : H →* Equiv.Perm (ReplicatedFibreLabel cls t) :=
    replicatedFibreLabelGroupAction rho iota cls hCls t ht
  let relabel : H →* Equiv.Perm {w : W // occupied (idx w)} := {
    toFun := fun h => (e.symm.trans (act h)).trans e
    map_one' := by
      apply Equiv.ext
      intro z
      change e (act 1 (e.symm z)) = z
      rw [map_one]
      exact e.apply_symm_apply z
    map_mul' := by
      intro k h
      apply Equiv.ext
      intro z
      change e (act (k * h) (e.symm z)) =
        e (act k (e.symm (e (act h (e.symm z)))))
      rw [map_mul, e.symm_apply_apply]
      rfl
  }
  exact (Equiv.Perm.ofSubtype
    (p := fun w : W => occupied (idx w))).comp relabel

/-- On an occupied coded point the global action is EXACTLY the
replicated-label action transported by e. -/
theorem replicatedFixedCarrierGroupAction_onReplicated
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (t : I → ℕ)
    (ht : ∀ (h : H) (i : I),
      t (iota h i) = t i)
    (idx : W → I)
    (occupied : I → Prop)
    (e : ReplicatedFibreLabel cls t ≃
        {w : W // occupied (idx w)})
    (h : H) (z : ReplicatedFibreLabel cls t) :
    replicatedFixedCarrierGroupAction
        rho iota cls hCls t ht idx occupied e h (e z).val =
      (e (replicatedFibreLabelGroupAction
        rho iota cls hCls t ht h z)).val := by
  classical
  change
    Equiv.Perm.ofSubtype
      ((e.symm.trans
        (replicatedFibreLabelGroupAction
          rho iota cls hCls t ht h)).trans e)
      (e z).val = _
  rw [Equiv.Perm.ofSubtype_apply_coe]
  simp

/-- On the complement of the occupied part set, the group action
fixes all points pointwise. -/
theorem replicatedFixedCarrierGroupAction_unoccupied
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (t : I → ℕ)
    (ht : ∀ (h : H) (i : I),
      t (iota h i) = t i)
    (idx : W → I)
    (occupied : I → Prop)
    (e : ReplicatedFibreLabel cls t ≃
        {w : W // occupied (idx w)})
    (h : H) (w : W)
    (hw : ¬occupied (idx w)) :
    replicatedFixedCarrierGroupAction
        rho iota cls hCls t ht idx occupied e h w = w := by
  classical
  change
    Equiv.Perm.ofSubtype
      ((e.symm.trans
        (replicatedFibreLabelGroupAction
          rho iota cls hCls t ht h)).trans e) w = w
  exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hw

/-- If the chosen coding identifies the original embedding j(x)
with the replicated zero-copy point (x,0), the resulting group
action extends the prescribed old action literally. -/
theorem replicatedFixedCarrierGroupAction_old
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (t : I → ℕ)
    (ht : ∀ (h : H) (i : I),
      t (iota h i) = t i)
    (hpos : ∀ x : S, 0 < t (cls x))
    (idx : W → I)
    (occupied : I → Prop)
    (e : ReplicatedFibreLabel cls t ≃
        {w : W // occupied (idx w)})
    (j : S → W)
    (hj : ∀ x : S,
      (e (replicatedFibreOldLabel cls t hpos x)).val = j x)
    (h : H) (x : S) :
    replicatedFixedCarrierGroupAction
        rho iota cls hCls t ht idx occupied e h (j x) =
      j (rho h x) := by
  calc
    replicatedFixedCarrierGroupAction
        rho iota cls hCls t ht idx occupied e h (j x) =
      replicatedFixedCarrierGroupAction
        rho iota cls hCls t ht idx occupied e h
          (e (replicatedFibreOldLabel cls t hpos x)).val := by rw [hj x]
    _ =
      (e (replicatedFibreLabelGroupAction
        rho iota cls hCls t ht h
          (replicatedFibreOldLabel cls t hpos x))).val :=
      replicatedFixedCarrierGroupAction_onReplicated
        rho iota cls hCls t ht idx occupied e h _
    _ = (e (replicatedFibreOldLabel cls t hpos (rho h x))).val := by
      rw [replicatedFibreOldLabel_equivariant]
    _ = j (rho h x) := hj (rho h x)

end SemigenericEPPA
