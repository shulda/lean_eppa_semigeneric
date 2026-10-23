import SemigenericEPPA.Structure.FixedGoodSelectedRawLiftData

/-!
# ONE fixed finite raw cover from an EXPLICIT good orbit seed

The certified positive coherent witness chooses its skeleton by
Classical.choose of a merely nonempty good effective-colour set.
The strictly weaker DLF criterion says that only SOME complete
congruence orbit is good; an arbitrary other good colour may have
a bad orbit. Thus the reference skeleton must be fixed to a
CHOSEN complete-orbit seed g0.

This theorem repeats the EXACT certified finite factorial gauge,
true quotient-indexed gauge, globally constant valuation skeleton,
literal old embedding and one joint original-language raw cover,
but takes g0 explicitly with a genuine reversal-fixed raw preimage.
There is no H-dependent choice or global saturation assumption.

All fixed-gauge, old E/F and raw embedding certificates from the
coherent construction are exported without change, and g0 is
literally the skeleton colour, not a proof-dependent random choice.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

theorem exists_fixedGoodSelectedRawLiftData_of_seed
    (Praw : RawRectanglePresentation d A)
    (g0 : G) (hGood : g0 ∈ d.selfReverseEffective) :
    ∃ (j : A → Fin (coherentPaddingSize A))
      (Q : IndexedGauge d.s
        (Quotient Praw.effectiveReduct.part × Fin (coherentPaddingSize A))
        (Quotient Praw.effectiveReduct.part))
      (R : IndexedGauge d.s
        (Quotient Praw.effectiveReduct.part × Fin (coherentPaddingSize A))
        (Quotient Q.toEffectiveGeometry.part))
      (K : EffectiveWitnessSkeleton Q.toEffectiveGeometry),
      let D : EffectiveGeometry d.s A := Praw.effectiveReduct
      let B := Q.toEffectiveGeometry
      let old : A → Quotient D.part × Fin (coherentPaddingSize A) :=
        D.factorialAuxiliaryOldMap j
      let ψ : A → EffectiveWitnessVertex B :=
        fun x => B.gaugeOldWitnessVertex R.vertexGauge (old x)
      ∃ J : FixedJointRawCover Praw K.toEffectiveGeometry ψ,
        Function.Injective j ∧
        (∀ z : Quotient D.part × Fin (coherentPaddingSize A),
          Q.label z = z.1) ∧
        (∀ z w : Quotient D.part × Fin (coherentPaddingSize A),
          B.part z w ↔ z.1 = w.1) ∧
        (∀ z : Quotient D.part × Fin (coherentPaddingSize A),
          R.label z = Quotient.mk B.part z) ∧
        (∀ i k : Quotient B.part,
          R.skeleton i k = g0) ∧
        (∀ z : Quotient D.part × Fin (coherentPaddingSize A),
          R.vertexGauge z (R.label z) = 1) ∧
        (∀ z w : Quotient D.part × Fin (coherentPaddingSize A),
          ¬B.part z w → R.effective z w = B.F z w) ∧
        (∀ q r : EffectiveWitnessPart B,
          K.colour q r = g0) ∧
        (∀ x y : A, B.part (old x) (old y) ↔ D.part x y) ∧
        (∀ x y : A, ¬D.part x y →
          B.F (old x) (old y) = D.F x y) ∧
        Function.Injective ψ ∧
        (∀ x y : A,
          K.toEffectiveGeometry.part (ψ x) (ψ y) ↔ Praw.part x y) ∧
        (∀ x y : A, ¬Praw.part x y →
          K.toEffectiveGeometry.F (ψ x) (ψ y) = D.F x y) ∧
        Finite (EffectiveWitnessVertex B) := by
  let D : EffectiveGeometry d.s A := Praw.effectiveReduct
  classical
  let W := Quotient D.part × Fin (coherentPaddingSize A)
  letI : Fintype (Quotient D.part) := Fintype.ofFinite _
  letI : LinearOrder (Quotient D.part) :=
    LinearOrder.lift' (Fintype.equivFin (Quotient D.part))
      (Fintype.equivFin (Quotient D.part)).injective
  obtain ⟨j, hj⟩ := exists_fixedFactorialOldInjection A
  have hGoodFixed : d.s g0 = g0 :=
    d.selfReverseEffective_subset_fixed hGood
  let P : IndexedGauge d.s A (Quotient D.part) :=
    D.constantQuotientIndexedGauge g0 hGoodFixed
  let Q : IndexedGauge d.s W (Quotient D.part) :=
    P.fixedUniformPaddingGauge g0 hGoodFixed
      (coherentPaddingSize A) j
  let B : EffectiveGeometry d.s W := Q.toEffectiveGeometry
  have hPLabel (x : A) :
      P.label x = Quotient.mk D.part x := rfl
  have hQLabel (z : W) : Q.label z = z.1 := rfl
  have hQDiag (z : W) : Q.vertexGauge z z.1 = 1 :=
    P.fixedUniformPaddingGauge_diagonal g0 hGoodFixed
      (coherentPaddingSize A) j z
  have hQConst (i k : Quotient D.part) :
      Q.skeleton i k = g0 := rfl
  have hFiniteW : Finite W := by
    infer_instance
  have hPOldF (x y : A) (hxy : ¬D.part x y) :
      B.F (P.fixedUniformPaddingOldMap j x)
        (P.fixedUniformPaddingOldMap j y) = D.F x y := by
    have hne : P.label x ≠ P.label y := by
      rw [hPLabel x, hPLabel y]
      intro heq
      exact hxy (Quotient.exact heq)
    calc
      B.F (P.fixedUniformPaddingOldMap j x)
          (P.fixedUniformPaddingOldMap j y) =
        P.toEffectiveGeometry.F x y :=
          P.fixedUniformPaddingOldMap_colour
            g0 hGoodFixed (fun _ _ => rfl)
              (coherentPaddingSize A) j hj x y hne
      _ = D.F x y :=
        D.constantQuotientIndexedGauge_cross
          g0 hGoodFixed x y hxy
  have hPositive : 0 < coherentPaddingSize A :=
    coherentPaddingSize_pos A
  obtain ⟨R, hRLabel, hRConst, hRDiag, _hRPart, hRF⟩ :=
    exists_fixedFibreGauge_onActualQuotient
      (s := d.s) (coherentPaddingSize A) hPositive Q
      hQLabel g0 hQConst
  have hRDiagOne (z : W) :
      R.vertexGauge z (R.label z) = 1 := by
    rw [hRDiag z, hQLabel z]
    exact hQDiag z
  let old : A → W := D.factorialAuxiliaryOldMap j
  have hOldMap (x : A) :
      P.fixedUniformPaddingOldMap j x = old x := by
    change (P.label x, j x) = (Quotient.mk D.part x, j x)
    rw [hPLabel x]
  have hBaseE (x y : A) :
      B.part (old x) (old y) ↔ D.part x y := by
    change Q.label (old x) = Q.label (old y) ↔ D.part x y
    rw [hQLabel (old x), hQLabel (old y)]
    change (Quotient.mk D.part x = Quotient.mk D.part y) ↔ D.part x y
    exact ⟨Quotient.exact, Quotient.sound⟩
  have hBaseF (x y : A) (hxy : ¬D.part x y) :
      B.F (old x) (old y) = D.F x y := by
    rw [← hOldMap x, ← hOldMap y]
    exact hPOldF x y hxy
  have hROldF (x y : W) (_hxy : ¬B.part x y) :
      R.effective x y = B.F x y :=
    hRF x y
  let skeleton : Quotient B.part → Quotient B.part → G :=
    fun _ _ => g0
  have hReverse : ∀ i k : Quotient B.part,
      skeleton k i = d.s (skeleton i k) := by
    intro i k
    exact hGoodFixed.symm
  let K : EffectiveWitnessSkeleton B :=
    B.indexedWitnessSkeleton skeleton hReverse
  have hKConst (q r : EffectiveWitnessPart B) :
      K.colour q r = g0 := rfl
  have hKOld (i k : Quotient B.part) (_ : i ≠ k) :
      K.colour (distinguishedWitnessPart B i)
        (distinguishedWitnessPart B k) = R.skeleton i k :=
    (hKConst _ _).trans (hRConst i k).symm
  let ψ : A → EffectiveWitnessVertex B :=
    fun x => B.gaugeOldWitnessVertex R.vertexGauge (old x)
  have hInjective : Function.Injective ψ := by
    intro x y hxy
    have hold : old x = old y :=
      B.gaugeOldWitnessVertex_injective R.vertexGauge hxy
    exact hj (congrArg Prod.snd hold)
  have hψE (x y : A) :
      K.toEffectiveGeometry.part (ψ x) (ψ y) ↔ D.part x y :=
    (B.gaugeOldWitnessVertex_part_iff
      R.vertexGauge K (old x) (old y)).trans (hBaseE x y)
  have hψF (x y : A) (hxy : ¬D.part x y) :
      K.toEffectiveGeometry.F (ψ x) (ψ y) = D.F x y := by
    have hcross : ¬B.part (old x) (old y) := by
      intro hb
      exact hxy ((hBaseE x y).mp hb)
    calc
      K.toEffectiveGeometry.F (ψ x) (ψ y) =
        B.F (old x) (old y) :=
          B.gaugeOldWitnessVertex_colour
            R hRLabel hROldF K hKOld (old x) (old y) hcross
      _ = D.F x y := hBaseF x y hxy
  have hFiniteWitness : Finite (EffectiveWitnessVertex B) := by
    letI : Finite W := hFiniteW
    exact B.finite_effectiveWitnessVertices

  have hBPart (z w : W) :
      B.part z w ↔ z.1 = w.1 := by
    change Q.label z = Q.label w ↔ z.1 = w.1
    rw [hQLabel z, hQLabel w]
  have hRawPart (x y : A) :
      K.toEffectiveGeometry.part (ψ x) (ψ y) ↔ Praw.part x y :=
    (hψE x y).trans (Praw.effectiveReduct_part x y)
  have hRawPhi (x y : A) (c : C)
      (hc : Praw.colour x y = some c) :
      d.phi c = K.toEffectiveGeometry.F (ψ x) (ψ y) := by
    have hxy : ¬D.part x y := by
      intro hp
      have hn : Praw.colour x y = none :=
        (Praw.colour_none_iff x y).2 hp
      rw [hc] at hn
      cases hn
    calc
      d.phi c = D.F x y :=
        Praw.effectiveReduct_crossColour x y c hc
      _ = K.toEffectiveGeometry.F (ψ x) (ψ y) :=
        (hψF x y hxy).symm
  letI : Finite (EffectiveWitnessVertex B) := hFiniteWitness
  obtain ⟨J⟩ :=
    exists_fixedJointRawCover Praw K.toEffectiveGeometry
      ψ hInjective hRawPart hRawPhi
  have hRawF (x y : A) (hxy : ¬Praw.part x y) :
      K.toEffectiveGeometry.F (ψ x) (ψ y) = D.F x y := by
    apply hψF x y
    intro hd
    exact hxy ((Praw.effectiveReduct_part x y).mp hd)
  exact ⟨j, Q, R, K, J, hj, hQLabel,
    hBPart, hRLabel, hRConst, hRDiagOne,
    hROldF, hKConst, hBaseE, hBaseF,
    hInjective, hRawPart, hRawF, hFiniteWitness⟩


end RawRectanglePresentation

end SemigenericEPPA
