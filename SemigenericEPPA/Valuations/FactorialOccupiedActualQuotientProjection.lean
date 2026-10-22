import SemigenericEPPA.Valuations.FactorialAuxiliaryOccupiedProjection
import SemigenericEPPA.Structure.FixedFibreQuotientGroupAction

/-!
# Reindex the genuine factorial projection to the actual E-quotient

The factorial auxiliary action and its Option-valued equivariant
selected-old projection are built together from one replica coding,
but initially their index action is on the original I=A/E.
For the subsequent two-layer witness, the required index type is
literally Quotient B.part of the fixed padded effective base B.

This theorem transports the same strict index action through the
canonical equivalence Quotient B.part ≃ I. It does NOT replace
the auxiliary action or the occupied projection. The projection
remains H-equivariant and class-compatible and sends every old
zero-copy label to itself; empty indices are fixed pointwise.

No global F-colour preservation by the padded old-label action
and no subsingleton assumption on G are required.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {A : Type v} [Fintype A]
variable {H : Type w} [Group H]
variable {s : AffineAntiInvolution G}

theorem EffectiveGeometry.exists_factorialProjection_onActualQuotient
    (D : EffectiveGeometry s A)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (B : EffectiveGeometry s
      (Quotient D.part × Fin (coherentPaddingSize A)))
    (hBPart : ∀ z w : Quotient D.part × Fin (coherentPaddingSize A),
      B.part z w ↔ z.1 = w.1)
    (S : Set A)
    (rhoS : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      D.part x.val y.val ↔
        D.part (rhoS h x).val (rhoS h y).val) :
    ∃ (iotaQ : H →* Equiv.Perm (Quotient B.part))
      (tau : H →* Equiv.Perm
        (Quotient D.part × Fin (coherentPaddingSize A)))
      (proj : (Quotient D.part × Fin (coherentPaddingSize A)) →
        Option S),
      let old : S → Quotient D.part × Fin (coherentPaddingSize A) :=
        fun x => (Quotient.mk D.part x.val, j x.val)
      let cls : S → Quotient B.part :=
        fun x => Quotient.mk B.part (old x)
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        Quotient.mk B.part (tau h z) =
          iotaQ h (Quotient.mk B.part z)) ∧
      (∀ (h : H) (x : S),
        tau h (old x) = old (rhoS h x)) ∧
      (∀ (h : H) (q : Quotient B.part),
        (¬∃ x : S, cls x = q) →
          iotaQ h q = q) ∧
      (∀ (z : Quotient D.part × Fin (coherentPaddingSize A)),
        (∃ x : S, cls x = Quotient.mk B.part z) →
          ∃ x : S, proj z = some x) ∧
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        proj (tau h z) = Option.map (rhoS h) (proj z)) ∧
      (∀ (z : Quotient D.part × Fin (coherentPaddingSize A))
        (x : S),
        proj z = some x →
          Quotient.mk B.part z = cls x) ∧
      (∀ x : S, proj (old x) = some x) := by
  obtain ⟨iota, tau, proj, hIndex, hOld, hFixed,
      _hUnused, hSome, hProj, hProjClass, hOldProj⟩ :=
    D.exists_factorialAuxiliaryAction_withOccupiedProjection
      j hj S rhoS hE
  let W : Type _ := Quotient D.part × Fin (coherentPaddingSize A)
  let old : S → W :=
    fun x => (Quotient.mk D.part x.val, j x.val)
  let cls : S → Quotient B.part :=
    fun x => Quotient.mk B.part (old x)
  have hPositive : 0 < coherentPaddingSize A :=
    coherentPaddingSize_pos A
  let e : Quotient B.part ≃ Quotient D.part :=
    fixedFibreQuotientEquiv (coherentPaddingSize A) hPositive B hBPart
  let iotaQ : H →* Equiv.Perm (Quotient B.part) :=
    fixedFibreQuotientGroupAction
      (coherentPaddingSize A) hPositive B hBPart iota
  have hIndexActual (h : H) (z : W) :
      Quotient.mk B.part (tau h z) =
        iotaQ h (Quotient.mk B.part z) :=
    fixedFibreQuotientGroupAction_compatible
      (coherentPaddingSize A) hPositive B hBPart iota tau hIndex h z
  have hOldActual (h : H) (x : S) :
      tau h (old x) = old (rhoS h x) := hOld h x
  have hEqClass (x : S) :
      e (cls x) = Quotient.mk D.part x.val := rfl
  have hEqLabel (z : W) :
      e (Quotient.mk B.part z) = z.1 := rfl
  have hFixedActual (h : H) (q : Quotient B.part)
      (hq : ¬∃ x : S, cls x = q) :
      iotaQ h q = q := by
    apply e.injective
    change iota h (e q) = e q
    apply hFixed h (e q)
    rintro ⟨x, hx⟩
    apply hq
    refine ⟨x, ?_⟩
    apply e.injective
    calc
      e (cls x) = Quotient.mk D.part x.val := hEqClass x
      _ = e q := hx
  have hSomeActual (z : W)
      (hz : ∃ x : S, cls x = Quotient.mk B.part z) :
      ∃ x : S, proj z = some x := by
    obtain ⟨x, hx⟩ := hz
    apply hSome z
    refine ⟨x, ?_⟩
    calc
      Quotient.mk D.part x.val = e (cls x) := (hEqClass x).symm
      _ = e (Quotient.mk B.part z) := congrArg e hx
      _ = z.1 := hEqLabel z
  have hClassActual (z : W) (x : S)
      (hx : proj z = some x) :
      Quotient.mk B.part z = cls x := by
    apply e.injective
    calc
      e (Quotient.mk B.part z) = z.1 := hEqLabel z
      _ = Quotient.mk D.part x.val := hProjClass z x hx
      _ = e (cls x) := (hEqClass x).symm
  refine ⟨iotaQ, tau, proj, hIndexActual, hOldActual,
    hFixedActual, hSomeActual, hProj, hClassActual, ?_⟩
  intro x
  exact hOldProj x

end SemigenericEPPA
