import SemigenericEPPA.Valuations.FactorialRelativeEffectiveWitnessAction

/-!
# Relative group actions on ONE PRESELECTED gauge presentation

The certified factorial-relative effective H-action theorem builds
all multipliers, reference twists, quotient actions, and a genuine
action on the full two-layer witness. It returns a gauge R, however,
inside its existential output, after H and the selected old S
have already been quantified.

For coherent EPPA, the witness and the old embedding must have been
fixed BEFORE S and H. Hence a consumer needs a theorem accepting
one PRESELECTED quotient-indexed gauge R, known to be E/F-equivalent
to the globally fixed factorial indexed gauge Q. The action must
act on the zero-section determined by EXACTLY this same R, not
an independently selected equivalent gauge.

This theorem is that stronger quantifier-order bridge. Every
group element still acts by a strict homomorphism, and every
multiplicative correction and auxiliary action is existentially
constructed from genuine E/F automorphisms of S alone. There is
no requirement that those automorphisms preserve effective F
on the old vertices outside S.

The fixed skeleton colour is chosen before S/H and the witness
group action preserves the full effective E/F geometry. Raw-colour
flip safety and raw-cover lifting remain separate.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {C : Type v} {A : Type w} [Fintype A]
variable {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace EffectiveGeometry

/-- Relative H-action over a FIXED quotient-indexed gauge R.
All selected H-group actions on the finite original A extend on
the SAME full two-layer witness, and its old zero-section is the
same fixed map determined by R for every S and H.

No H-dependent gauge or old injection is introduced. -/
theorem exists_factorialRelativeHAction_onFixedGauge
    (D : EffectiveGeometry d.s A)
    (hGood : d.selfReverseEffective.Nonempty)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (Q : IndexedGauge d.s
      (Quotient D.part × Fin (coherentPaddingSize A))
      (Quotient D.part))
    (hQlabel : ∀ z : Quotient D.part × Fin (coherentPaddingSize A),
      Q.label z = z.1)
    (hOldColour : ∀ x y : A, ¬D.part x y →
      Q.toEffectiveGeometry.F
        (D.factorialAuxiliaryOldMap j x)
        (D.factorialAuxiliaryOldMap j y) = D.F x y)
    (R : IndexedGauge d.s
      (Quotient D.part × Fin (coherentPaddingSize A))
      (Quotient Q.toEffectiveGeometry.part))
    (hRlabel : ∀ w : Quotient D.part × Fin (coherentPaddingSize A),
      R.label w = Quotient.mk Q.toEffectiveGeometry.part w)
    (hRconstant : ∀ i k : Quotient Q.toEffectiveGeometry.part,
      R.skeleton i k = Classical.choose hGood)
    (hRdiagonal : ∀ w : Quotient D.part × Fin (coherentPaddingSize A),
      R.vertexGauge w (R.label w) = 1)
    (hRF : ∀ x y : Quotient D.part × Fin (coherentPaddingSize A),
      R.toEffectiveGeometry.F x y = Q.toEffectiveGeometry.F x y)
    (S : Set A)
    (rho : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      D.part (rho h x).val (rho h y).val ↔
        D.part x.val y.val)
    (hF : ∀ (h : H) (x y : S), ¬D.part x.val y.val →
      D.F (rho h x).val (rho h y).val = D.F x.val y.val) :
    ∃ (K : EffectiveWitnessSkeleton Q.toEffectiveGeometry)
      (Theta : H →* Equiv.Perm
        (EffectiveWitnessVertex Q.toEffectiveGeometry)),
      (∀ q r : EffectiveWitnessPart Q.toEffectiveGeometry,
        K.colour q r = Classical.choose hGood) ∧
      (∀ (h : H) (x : S),
        Theta h
          (Q.toEffectiveGeometry.gaugeOldWitnessVertex R.vertexGauge
            (D.factorialAuxiliaryOldMap j x.val)) =
          Q.toEffectiveGeometry.gaugeOldWitnessVertex R.vertexGauge
            (D.factorialAuxiliaryOldMap j (rho h x).val)) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex Q.toEffectiveGeometry),
        K.toEffectiveGeometry.part (Theta h X) (Theta h Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex Q.toEffectiveGeometry),
        ¬K.toEffectiveGeometry.part X Y →
        K.toEffectiveGeometry.F (Theta h X) (Theta h Y) =
          K.toEffectiveGeometry.F X Y) := by
  let B : EffectiveGeometry d.s
      (Quotient D.part × Fin (coherentPaddingSize A)) :=
    Q.toEffectiveGeometry
  have hBpart : ∀ z w : Quotient D.part × Fin (coherentPaddingSize A),
      B.part z w ↔ z.1 = w.1 := by
    intro z w
    change Q.label z = Q.label w ↔ z.1 = w.1
    rw [hQlabel z, hQlabel w]
  let old : A → Quotient D.part × Fin (coherentPaddingSize A) :=
    D.factorialAuxiliaryOldMap j
  obtain ⟨iota, tau, hIndex, hOld, _hFixed, _hUnused,
      hImage, _hImageE, hImageF⟩ :=
    D.exists_factorialAuxiliaryAction_preservingSelectedEF
      j hj B hBpart hOldColour S rho hE hF
  have hPositive : 0 < coherentPaddingSize A :=
    coherentPaddingSize_pos A
  obtain ⟨iotaQ, hQuotient⟩ :=
    exists_fixedFibreQuotientGroupAction
      (s := d.s) (coherentPaddingSize A) hPositive B
      hBpart iota tau hIndex
  let T : Set (Quotient D.part × Fin (coherentPaddingSize A)) :=
    embeddedOldSubset old S
  have hT : ∀ (h : H)
      (z : Quotient D.part × Fin (coherentPaddingSize A)),
      z ∈ T ↔ tau h z ∈ T :=
    hImage
  have hSelF : ∀ (h : H) (x y : T),
      R.label x.val ≠ R.label y.val →
      R.toEffectiveGeometry.F (tau h x.val) (tau h y.val) =
        R.toEffectiveGeometry.F x.val y.val := by
    intro h x y hxy
    have hcross : ¬B.part x.val y.val := by
      intro hxyB
      apply hxy
      rw [hRlabel x.val, hRlabel y.val]
      exact Quotient.sound hxyB
    calc
      R.toEffectiveGeometry.F (tau h x.val) (tau h y.val) =
        B.F (tau h x.val) (tau h y.val) :=
          hRF _ _
      _ = B.F x.val y.val := hImageF h x y hcross
      _ = R.toEffectiveGeometry.F x.val y.val :=
          (hRF _ _).symm
  obtain ⟨K, Theta, hK, hThetaOld, hThetaE, hThetaF⟩ :=
    R.exists_relativeFullEffectiveGroupLift
      B hRlabel T hGood hRconstant hRdiagonal
      tau iotaQ hT hQuotient hSelF
  refine ⟨K, Theta, hK, ?_, hThetaE, hThetaF⟩
  intro h x
  have hx : old x.val ∈ T := ⟨x, rfl⟩
  have hImageOld := hThetaOld h (old x.val) hx
  rw [hOld h x] at hImageOld
  exact hImageOld

end EffectiveGeometry

end SemigenericEPPA
