import SemigenericEPPA.Valuations.NontrivialFactorialAuxiliaryAction
import SemigenericEPPA.Valuations.ReplicatedOccupiedProjection

/-!
# Factorial old-label H-actions together with their actual occupied projection

The previous factorial auxiliary H-action existential theorem
constructed a fixed-carrier permutation action by conjugating
replicated selected old fibres. For the NONTRIVIAL-G coherent
flip-safety argument we must retain its SAME replica coding:
otherwise an unrelated equivariant projection cannot be inferred
from an arbitrary ambient extension of the old H-action.

Here we construct simultaneously, on the SAME globally prechosen
old-label carrier W=(A/E)×Fin(|A|!):

* iota, the strict quotient index H-action fixing unvisited parts;
* tau, the strict full auxiliary old-label H-action extending S;
* proj : W → Option S, equal to None on unvisited parts;
* totality of proj on occupied parts, exact H-equivariance,
  class compatibility and a zero-copy identity proj(old(x))=some x.

No effective F-invariance outside S, no assumption G=1, and no
H-dependent change to W or its old injection j is used. The
projection remains undefined on unoccupied classes and is
sufficient for the certified different-old-index swapped-pair
geometry in the full two-layer witness.
-/

namespace SemigenericEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {A : Type w} [Fintype A]
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- Every induced E-preserving H-action on S has a factorial
auxiliary extension AND an equivariant partial projection using
ONE actual replica coding. The old injection j is chosen before
S/H, and every old selected point projects to itself. -/
theorem exists_factorialAuxiliaryAction_withOccupiedProjection
    (D : EffectiveGeometry s A)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (S : Set A)
    (rho : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      D.part x.val y.val ↔
        D.part (rho h x).val (rho h y).val) :
    ∃ (iota : H →* Equiv.Perm (Quotient D.part))
      (tau : H →* Equiv.Perm
        (Quotient D.part × Fin (coherentPaddingSize A)))
      (proj : (Quotient D.part × Fin (coherentPaddingSize A)) →
        Option S),
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        (tau h z).1 = iota h z.1) ∧
      (∀ (h : H) (x : S),
        tau h (Quotient.mk D.part x.val, j x.val) =
          (Quotient.mk D.part (rho h x).val, j (rho h x).val)) ∧
      (∀ (h : H) (i : Quotient D.part),
        (¬∃ x : S, Quotient.mk D.part x.val = i) →
          iota h i = i) ∧
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        (¬∃ x : S, Quotient.mk D.part x.val = z.1) →
          tau h z = z) ∧
      (∀ (z : Quotient D.part × Fin (coherentPaddingSize A)),
        (∃ x : S, Quotient.mk D.part x.val = z.1) →
          ∃ x : S, proj z = some x) ∧
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        proj (tau h z) = Option.map (rho h) (proj z)) ∧
      (∀ (z : Quotient D.part × Fin (coherentPaddingSize A))
        (x : S), proj z = some x →
          z.1 = Quotient.mk D.part x.val) ∧
      (∀ x : S,
        proj (Quotient.mk D.part x.val, j x.val) = some x) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  let cls : S → Quotient D.part :=
    fun x => Quotient.mk D.part x.val
  obtain ⟨iota, hiota, hFixed⟩ :=
    D.exists_occupiedQuotientGroupAction_fixed S rho hE
  have hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x) := by
    intro h x
    exact (hiota h x).symm
  let t : Quotient D.part → ℕ :=
    oldClassFibreMultiplicity cls (coherentPaddingSize A)
  obtain ⟨hPos, hSize, ht⟩ :=
    factorialOldFibreMultiplicity_laws
      (Subtype.val : S → A) Subtype.val_injective cls rho iota hCls
  let hFin (i : ReplicatedOccupiedIndex cls) :
      Fintype (ReplicatedOldFibre cls i) := by
    classical
    infer_instance
  have hSizeExact (i : ReplicatedOccupiedIndex cls) :
      (@Fintype.card (ReplicatedOldFibre cls i) (hFin i)) *
        t i.val = coherentPaddingSize A := by
    have h := hSize i
    rw [occupiedOldClassFibreCard_eq cls i (hFin i)] at h
    exact h
  let jClass (i : ReplicatedOccupiedIndex cls)
      (x : ReplicatedOldFibre cls i) :
      Fin (coherentPaddingSize A) := j x.val.val
  have hjClass (i : ReplicatedOccupiedIndex cls) :
      Function.Injective (jClass i) := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hj hxy
  obtain ⟨e, hCoding, hOldCoding0⟩ :=
    exists_exactReplicatedOccupiedCoding cls t
      (coherentPaddingSize A) hFin hPos hSizeExact jClass hjClass
  let occupied : Quotient D.part → Prop :=
    fun i => ∃ x : S, cls x = i
  let tau : H →* Equiv.Perm
      (Quotient D.part × Fin (coherentPaddingSize A)) :=
    replicatedFixedCarrierGroupAction rho iota cls hCls
      t ht Prod.fst occupied e
  let proj : (Quotient D.part × Fin (coherentPaddingSize A)) →
      Option S :=
    replicatedOccupiedProjection cls t Prod.fst occupied e
  have hIndex (h : H)
      (z : Quotient D.part × Fin (coherentPaddingSize A)) :
      (tau h z).1 = iota h z.1 :=
    replicatedFixedCarrierGroupAction_class
      rho iota cls hCls t ht Prod.fst occupied
      hFixed e hCoding h z
  have hPosS : ∀ x : S, 0 < t (cls x) :=
    fun x => hPos ⟨cls x, ⟨x, rfl⟩⟩
  have hOldCoding (x : S) :
      (e (replicatedFibreOldLabel cls t hPosS x)).val =
        (cls x, j x.val) := by
    simpa only [jClass] using hOldCoding0 x
  have hOld (h : H) (x : S) :
      tau h (cls x, j x.val) =
        (cls (rho h x), j (rho h x).val) :=
    replicatedFixedCarrierGroupAction_old
      rho iota cls hCls t ht hPosS Prod.fst occupied
      e (fun x : S => (cls x, j x.val)) hOldCoding h x
  have hProjectionSome
      (z : Quotient D.part × Fin (coherentPaddingSize A))
      (hz : occupied z.1) :
      ∃ x : S, proj z = some x :=
    replicatedOccupiedProjection_some cls t Prod.fst occupied
      e z hz
  have hProj (h : H)
      (z : Quotient D.part × Fin (coherentPaddingSize A)) :
      proj (tau h z) = Option.map (rho h) (proj z) :=
    replicatedOccupiedProjection_equivariant
      rho iota cls hCls t ht Prod.fst occupied e h z
  have hProjClass
      (z : Quotient D.part × Fin (coherentPaddingSize A))
      (x : S) (hx : proj z = some x) :
      z.1 = cls x := by
    by_cases hz : occupied z.1
    · have heq : (e.symm ⟨z, hz⟩).1 = x := by
        have hh : some (e.symm ⟨z, hz⟩).1 = some x := by
          simpa [proj, replicatedOccupiedProjection, hz] using hx
        exact Option.some.inj hh
      have hLift : (e (e.symm ⟨z, hz⟩)).val = z :=
        congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)
      calc
        z.1 = (e (e.symm ⟨z, hz⟩)).val.1 := by rw [hLift]
        _ = cls (e.symm ⟨z, hz⟩).1 := hCoding _
        _ = cls x := congrArg cls heq
    · have hn : proj z = none := by
        simp [proj, replicatedOccupiedProjection, hz]
      rw [hn] at hx
      cases hx
  have hOldProjection (x : S) :
      proj (cls x, j x.val) = some x := by
    have hx : occupied (cls x) := ⟨x, rfl⟩
    let zero : ReplicatedFibreLabel cls t :=
      replicatedFibreOldLabel cls t hPosS x
    have heq : e zero =
        (⟨(cls x, j x.val), hx⟩ :
          {z : Quotient D.part × Fin (coherentPaddingSize A) //
            occupied z.1}) :=
      Subtype.ext (hOldCoding x)
    have hinv :
        e.symm (⟨(cls x, j x.val), hx⟩ :
          {z : Quotient D.part × Fin (coherentPaddingSize A) //
            occupied z.1}) = zero := by
      rw [← heq, e.symm_apply_apply]
    simp only [proj, replicatedOccupiedProjection, dif_pos hx]
    rw [hinv]
    rfl
  refine ⟨iota, tau, proj, hIndex, ?_, ?_, ?_,
    ?_, hProj, ?_, hOldProjection⟩
  · intro h x
    exact hOld h x
  · intro h i hi
    exact hFixed h i hi
  · intro h z hz
    exact replicatedFixedCarrierGroupAction_unoccupied
      rho iota cls hCls t ht Prod.fst occupied e h z hz
  · intro z hz
    exact hProjectionSome z hz
  · intro z x hx
    exact hProjClass z x hx

end EffectiveGeometry

end SemigenericEPPA
