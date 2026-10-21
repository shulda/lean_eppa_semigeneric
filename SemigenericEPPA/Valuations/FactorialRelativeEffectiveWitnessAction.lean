import SemigenericEPPA.Structure.IndexedGaugeReindexing
import SemigenericEPPA.Valuations.FactorialSelectedOldEFAction
import SemigenericEPPA.Valuations.SelectedRelativeFullEffectiveGroupLift
import SemigenericEPPA.Algebra.CoherentPaddingSize

/-!
# Assemble genuine relative H-actions on the fixed factorial effective base

An arbitrary finite original effective E-rectangle D on A has a fixed
old injection j into W=(A/E)×Fin(|A|!). Let Q be a chosen global
constant-good indexed gauge on W, exactly extending D's old E/F
colours and with all diagonal incidence coordinates normalized to 1.

The factorial action construction gives an auxiliary group action
tau:H→Perm W and an index action on A/E for ANY H acting by
E/F-automorphisms only on a selected induced old S⊆A. It need NOT
preserve F outside the embedded image old(S).

The actual selected image T=old(S) is invariant and its E/F matrix
is preserved. Using the canonical equivalence (Quotient B.part)≃A/E
we reindex Q along the true quotient of B=Q.toEffectiveGeometry;
the resulting gauge R has R.label w=[w] and exactly the same E/F.
Its skeleton is the same globally chosen good constant and its
diagonal rows remain 1.

The previously certified selected-substructure multiplier/reference
construction then returns a genuine action H→Aut of the SAME
two-layer valuation witness on B, extending the fixed old embedding
of S pointwise in every gauge incidence coordinate.

All H-indexed multipliers, reference twists and the quotient-index
action are CONSTRUCTED, not supplied. Only the initial fixed Q and j
are inputs. This is an effective group-action theorem, not yet the
raw-colour safety or complete coherent EPPA theorem.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {C : Type v} {A : Type w} [Fintype A]
variable {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace EffectiveGeometry

/-- Given ONE fixed factorial effective E/F base Q on W, every
genuine H-action on every selected old induced S admits a strict
effective witness H-action, extending all selected old vertices.
There is no supplementary auxiliary-label, quotient-index, gauge
multiplier, or reference-twist existence assumption.

The output R is the exact reindexed gauge of Q on the actual
Quotient B.part; it remains an E/F-equivalent fixed representation.
-/
theorem exists_factorialRelativeEffectiveWitnessAction
    (D : EffectiveGeometry d.s A)
    (hGood : d.selfReverseEffective.Nonempty)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (Q : IndexedGauge d.s
      (Quotient D.part × Fin (coherentPaddingSize A))
      (Quotient D.part))
    (hQlabel : ∀ z : Quotient D.part × Fin (coherentPaddingSize A),
      Q.label z = z.1)
    (hQconstant : ∀ i k : Quotient D.part,
      Q.skeleton i k = Classical.choose hGood)
    (hQdiagonal : ∀ z : Quotient D.part × Fin (coherentPaddingSize A),
      Q.vertexGauge z z.1 = 1)
    (hOldColour : ∀ x y : A, ¬D.part x y →
      Q.toEffectiveGeometry.F
        (D.factorialAuxiliaryOldMap j x)
        (D.factorialAuxiliaryOldMap j y) = D.F x y)
    (S : Set A)
    (rho : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      D.part (rho h x).val (rho h y).val ↔
        D.part x.val y.val)
    (hF : ∀ (h : H) (x y : S), ¬D.part x.val y.val →
      D.F (rho h x).val (rho h y).val = D.F x.val y.val) :
    ∃ (R : IndexedGauge d.s
        (Quotient D.part × Fin (coherentPaddingSize A))
        (Quotient Q.toEffectiveGeometry.part))
      (K : EffectiveWitnessSkeleton Q.toEffectiveGeometry)
      (Theta : H →* Equiv.Perm
        (EffectiveWitnessVertex Q.toEffectiveGeometry)),
      (∀ z : Quotient D.part × Fin (coherentPaddingSize A),
        R.label z = Quotient.mk Q.toEffectiveGeometry.part z) ∧
      (∀ z : Quotient D.part × Fin (coherentPaddingSize A),
        R.vertexGauge z (R.label z) = 1) ∧
      (∀ x y : Quotient D.part × Fin (coherentPaddingSize A),
        R.toEffectiveGeometry.F x y = Q.toEffectiveGeometry.F x y) ∧
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
  obtain ⟨R, hRlabel, hRconstant, hRdiagonal, _hRpart, hRF⟩ :=
    exists_fixedFibreGauge_onActualQuotient
      (s := d.s) (coherentPaddingSize A) hPositive Q
      hQlabel (Classical.choose hGood) hQconstant
  have hDiagonal : ∀ z : Quotient D.part × Fin (coherentPaddingSize A),
      R.vertexGauge z (R.label z) = 1 := by
    intro z
    rw [hRdiagonal z, hQlabel z]
    exact hQdiagonal z
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
      B hRlabel T hGood hRconstant hDiagonal
      tau iotaQ hT hQuotient hSelF
  refine ⟨R, K, Theta, hRlabel, hDiagonal, hRF, hK,
    ?_, hThetaE, hThetaF⟩
  intro h x
  have hx : old x.val ∈ T := ⟨x, rfl⟩
  have hImageOld :=
    hThetaOld h (old x.val) hx
  rw [hOld h x] at hImageOld
  exact hImageOld

end EffectiveGeometry

end SemigenericEPPA
