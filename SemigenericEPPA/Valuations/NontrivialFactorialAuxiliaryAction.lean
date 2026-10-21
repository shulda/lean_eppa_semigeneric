import SemigenericEPPA.Valuations.OccupiedQuotientActionFixed
import SemigenericEPPA.Valuations.ReplicatedOccupiedProjection
import SemigenericEPPA.Algebra.ExactReplicatedOccupiedCoding
import SemigenericEPPA.Algebra.FactorialOldFibreMultiplicities
import SemigenericEPPA.Algebra.OldClassFibreCardInstance
import Mathlib.Data.Fintype.Prod

/-!
# A prechosen factorial carrier supports every induced-substructure H-action

This is the group/part-label geometric gate for the *nontrivial*
effective group sector. The prior G=1 safe factorial action theorem
used a Subsingleton G assumption to preserve all effective colours.
Here we prove precisely the group-action and class-compatibility
conclusion, which in fact does NOT need any assumption on G at all.

Given a finite old geometry D on A, choose M=|A|! and ONE fixed
injection j:A→Fin M before choosing an induced old subset S or a
finite group H. For any genuine action of H on S preserving the
restricted E-relation:

* construct the actual H-action iota on the original E-class quotient
  which fixes every class not meeting S;
* use factorial divisibility to replicate each occupied S-class into
  its prechosen whole fibre Fin M, preserving the original injection j;
* obtain a strict action rhoFull:H→Perm((A/E)×Fin M) on the ENTIRE
  fixed carrier;
* prove rhoFull(h)([x],j(x))=([hx],j(hx)) for each old x in S;
* prove rhoFull covers iota on ALL points and is pointwise trivial
  on every unoccupied class.

No preservation of old F-colours on A outside S is assumed or
claimed. Those labels may be used with the separate relative gauge
multipliers and reference twists of the nontrivial-G construction.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {A : Type v} [Fintype A]
variable {H : Type w} [Group H]
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- Fix a factorial-size carrier and old injection before S and H.
Every actual E-preserving group action on S extends to compatible
strict actions on the E-index sort and the same whole padded carrier.

The returned action does NOT have to preserve all old effective
colours outside S: it is the auxiliary LABEL action required by the
nontrivial-G relative effective witness-lift theorem. -/
theorem exists_factorialAuxiliaryGroupActions
    (D : EffectiveGeometry s A)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (S : Set A)
    (rho : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      D.part x.val y.val ↔
        D.part (rho h x).val (rho h y).val) :
    ∃ (iota : H →* Equiv.Perm (Quotient D.part))
        (rhoFull : H →* Equiv.Perm
          (Quotient D.part × Fin (coherentPaddingSize A))),
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        (rhoFull h z).1 = iota h z.1) ∧
      (∀ (h : H) (x : S),
        rhoFull h (Quotient.mk D.part x.val, j x.val) =
          (Quotient.mk D.part (rho h x).val, j (rho h x).val)) ∧
      (∀ (h : H) (i : Quotient D.part),
        (¬∃ x : S, Quotient.mk D.part x.val = i) →
          iota h i = i) ∧
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        (¬∃ x : S, Quotient.mk D.part x.val = z.1) →
          rhoFull h z = z) := by
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
  obtain ⟨e, hCoding, hOldCoding⟩ :=
    exists_exactReplicatedOccupiedCoding cls t
      (coherentPaddingSize A) hFin hPos hSizeExact jClass hjClass
  let occupied : Quotient D.part → Prop :=
    fun i => ∃ x : S, cls x = i
  let rhoFull : H →* Equiv.Perm
      (Quotient D.part × Fin (coherentPaddingSize A)) :=
    replicatedFixedCarrierGroupAction rho iota cls hCls
      t ht Prod.fst occupied e
  have hIndex (h : H)
      (z : Quotient D.part × Fin (coherentPaddingSize A)) :
      (rhoFull h z).1 = iota h z.1 :=
    replicatedFixedCarrierGroupAction_class
      rho iota cls hCls t ht Prod.fst occupied
      hFixed e hCoding h z
  have hPosS : ∀ x : S, 0 < t (cls x) :=
    fun x => hPos ⟨cls x, ⟨x, rfl⟩⟩
  have hjOld (x : S) :
      (e (replicatedFibreOldLabel cls t hPosS x)).val =
        (cls x, j x.val) := by
    simpa only [jClass] using hOldCoding x
  have hOld (h : H) (x : S) :
      rhoFull h (cls x, j x.val) =
        (cls (rho h x), j (rho h x).val) :=
    replicatedFixedCarrierGroupAction_old
      rho iota cls hCls t ht hPosS Prod.fst occupied
        e (fun x : S => (cls x, j x.val)) hjOld h x
  refine ⟨iota, rhoFull, hIndex, ?_, ?_, ?_⟩
  · intro h x
    exact hOld h x
  · intro h i hi
    exact hFixed h i hi
  · intro h z hz
    exact replicatedFixedCarrierGroupAction_unoccupied
      rho iota cls hCls t ht Prod.fst occupied e h z hz

end EffectiveGeometry

end SemigenericEPPA
