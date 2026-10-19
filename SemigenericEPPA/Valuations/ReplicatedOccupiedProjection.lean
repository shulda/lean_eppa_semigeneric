import SemigenericEPPA.Valuations.ReplicatedFixedCarrierAction

/-!
# The canonical equivariant projection from replicated occupied fibres

Once a fixed witness carrier W is identified over its OCCUPIED parts
with the genuine old-replica bundle Σ x:S, Fin(t(class x)), there is a
canonical projection from each occupied witness point to its actual old
vertex x.  The projection takes value None on unoccupied parts.

The strict H-action constructed by conjugating the replica action
then:
* covers the stipulated H-action on all E-class indices;
* fixes every unoccupied point;
* commutes exactly with the partial (Option-valued) projection.

These properties are the precise input to the proved
OccupiedProjectionFlipSafety theorem.  No false global projection to
old vertices is asserted on unoccupied parts.
-/

namespace SemigenericEPPA

universe u v w z

variable {H : Type u} [Group H]
variable {S : Type v} {I : Type w} {W : Type z}

/-- The old-label projection from the replicated occupied portion
of W, undefined (None) on the complement. -/
noncomputable def replicatedOccupiedProjection
    (cls : S → I) (t : I → ℕ)
    (idx : W → I) (occupied : I → Prop)
    (e : ReplicatedFibreLabel cls t ≃
      {w : W // occupied (idx w)})
    (w : W) : Option S := by
  classical
  exact if hw : occupied (idx w) then
    some (e.symm ⟨w, hw⟩).1
  else none

/-- Every occupied witness point has a real old-label projection. -/
theorem replicatedOccupiedProjection_some
    (cls : S → I) (t : I → ℕ)
    (idx : W → I) (occupied : I → Prop)
    (e : ReplicatedFibreLabel cls t ≃
      {w : W // occupied (idx w)})
    (w : W) (hw : occupied (idx w)) :
    ∃ x : S,
      replicatedOccupiedProjection cls t idx occupied e w =
        some x := by
  classical
  refine ⟨(e.symm ⟨w, hw⟩).1, ?_⟩
  simp [replicatedOccupiedProjection, hw]

/-- Given a coding e that respects original E-class labels,
the conjugated H-action on fixed W has precisely the selected
class-index action iota. Unoccupied indices are fixed as assumed;
no global E-preservation by the S-label action is imposed. -/
theorem replicatedFixedCarrierGroupAction_class
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
    (hFixed : ∀ (h : H) (i : I),
      ¬occupied i → iota h i = i)
    (e : ReplicatedFibreLabel cls t ≃
      {w : W // occupied (idx w)})
    (hCoding : ∀ z : ReplicatedFibreLabel cls t,
      idx (e z).val = cls z.1)
    (h : H) (w : W) :
    idx (replicatedFixedCarrierGroupAction
        rho iota cls hCls t ht idx occupied e h w) =
      iota h (idx w) := by
  classical
  by_cases hw : occupied (idx w)
  · let z : ReplicatedFibreLabel cls t := e.symm ⟨w, hw⟩
    have hwz : (e z).val = w :=
      congrArg Subtype.val (e.apply_symm_apply ⟨w, hw⟩)
    have hfst :
        (replicatedFibreLabelGroupAction
          rho iota cls hCls t ht h z).1 = rho h z.1 := rfl
    calc
      idx (replicatedFixedCarrierGroupAction
          rho iota cls hCls t ht idx occupied e h w) =
        idx (replicatedFixedCarrierGroupAction
          rho iota cls hCls t ht idx occupied e h (e z).val) := by
            rw [hwz]
      _ = idx (e (replicatedFibreLabelGroupAction
          rho iota cls hCls t ht h z)).val := by
            rw [replicatedFixedCarrierGroupAction_onReplicated]
      _ = cls (replicatedFibreLabelGroupAction
          rho iota cls hCls t ht h z).1 := hCoding _
      _ = iota h (cls z.1) := by rw [hfst, hCls]
      _ = iota h (idx w) := by rw [← hCoding z, hwz]
  · calc
      idx (replicatedFixedCarrierGroupAction
          rho iota cls hCls t ht idx occupied e h w) =
        idx w := congrArg idx
          (replicatedFixedCarrierGroupAction_unoccupied
            rho iota cls hCls t ht idx occupied e h w hw)
      _ = iota h (idx w) := (hFixed h (idx w) hw).symm

/-- The occupied old-label projection commutes with the strict
group action, with None preserved on unoccupied points. -/
theorem replicatedOccupiedProjection_equivariant
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
    (h : H) (w : W) :
    replicatedOccupiedProjection cls t idx occupied e
      (replicatedFixedCarrierGroupAction
        rho iota cls hCls t ht idx occupied e h w) =
      Option.map (rho h)
        (replicatedOccupiedProjection cls t idx occupied e w) := by
  classical
  by_cases hw : occupied (idx w)
  · let z : ReplicatedFibreLabel cls t := e.symm ⟨w, hw⟩
    have hwz : (e z).val = w :=
      congrArg Subtype.val (e.apply_symm_apply ⟨w, hw⟩)
    have hact :
        replicatedFixedCarrierGroupAction
          rho iota cls hCls t ht idx occupied e h w =
        (e (replicatedFibreLabelGroupAction
          rho iota cls hCls t ht h z)).val := by
      rw [← hwz]
      exact replicatedFixedCarrierGroupAction_onReplicated
        rho iota cls hCls t ht idx occupied e h z
    have hw' : occupied (idx
        (replicatedFixedCarrierGroupAction
          rho iota cls hCls t ht idx occupied e h w)) := by
      rw [hact]
      exact (e (replicatedFibreLabelGroupAction
        rho iota cls hCls t ht h z)).property
    have hp : replicatedOccupiedProjection cls t idx occupied e w =
        some z.1 := by
      simp [replicatedOccupiedProjection, hw, z]
    have hp' : replicatedOccupiedProjection cls t idx occupied e
          (replicatedFixedCarrierGroupAction
            rho iota cls hCls t ht idx occupied e h w) =
        some (replicatedFibreLabelGroupAction
          rho iota cls hCls t ht h z).1 := by
      have heq : (⟨replicatedFixedCarrierGroupAction
          rho iota cls hCls t ht idx occupied e h w, hw'⟩ :
            {w : W // occupied (idx w)}) =
          e (replicatedFibreLabelGroupAction
            rho iota cls hCls t ht h z) := Subtype.ext hact
      simp only [replicatedOccupiedProjection, dif_pos hw']
      rw [heq, e.symm_apply_apply]
    calc
      replicatedOccupiedProjection cls t idx occupied e
          (replicatedFixedCarrierGroupAction
            rho iota cls hCls t ht idx occupied e h w) =
        some (replicatedFibreLabelGroupAction
          rho iota cls hCls t ht h z).1 := hp'
      _ = some (rho h z.1) := rfl
      _ = Option.map (rho h)
          (replicatedOccupiedProjection cls t idx occupied e w) := by
            rw [hp]
            rfl
  · have hfix :=
      replicatedFixedCarrierGroupAction_unoccupied
        rho iota cls hCls t ht idx occupied e h w hw
    calc
      replicatedOccupiedProjection cls t idx occupied e
          (replicatedFixedCarrierGroupAction
            rho iota cls hCls t ht idx occupied e h w) =
        replicatedOccupiedProjection cls t idx occupied e w :=
          congrArg (replicatedOccupiedProjection cls t idx occupied e) hfix
      _ = none := by simp [replicatedOccupiedProjection, hw]
      _ = Option.map (rho h)
          (replicatedOccupiedProjection cls t idx occupied e w) := by
            simp [replicatedOccupiedProjection, hw]

end SemigenericEPPA
