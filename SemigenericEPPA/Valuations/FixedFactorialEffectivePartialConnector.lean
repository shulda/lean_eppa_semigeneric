import SemigenericEPPA.Valuations.IndexedGaugePartialEffectiveConnector
import SemigenericEPPA.Valuations.FactorialPartialLabelPermutations
import SemigenericEPPA.Structure.FixedFibreQuotientGroupAction

/-!
# Every old partial E/F map extends on ONE fixed factorial valuation witness

Fix a finite original effective geometry D, one injection
j:A→Fin(|A|!) chosen independently of all partial arrows, a
factorial padded effective base B over (A/E)×Fin(|A|!), a
preselected actual-quotient indexed gauge R representing B,
and a single valuation skeleton K matching R on old neutral
parts.

For any genuine injective partial E/F map p:S→A, the certified
factorial permutation theorem produces pi on the SAME old-label
carrier and iota on its original imaginary sort. Transport the
same iota to the ACTUAL Quotient B.part via the canonical
nonempty-fibre equivalence.

On the literal image old(S), pi transports exactly p, preserving
E/F by the fixed induced old embedding. The certified arbitrary
indexed-gauge partial multiplier theorem and the full twisted
valuation witness construction then produce ONE genuine effective
automorphism of the originally fixed K, extending precisely
the gauge-valued old zero-section.

No witness, gauge, skeleton, original injection or coordinate
convention is selected anew for a particular p. This is the
individual effective connector gate needed by the existing
fixed raw cover; the next step lifts the same automorphism to
the original R_c language on the same zero section.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [Fintype A]
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- ONE finite factorial base B and ONE skeleton K support actual
effective automorphism extensions of EVERY injective old partial
E/F-isomorphism on the SAME globally fixed gauge zero-section.

The target is literal old(p x), not merely an isomorphic recoding
or an independently chosen canonical quotient-gauge embedding. -/
theorem exists_fixedFactorialEffectivePartialConnector
    (D : EffectiveGeometry s A)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (B : EffectiveGeometry s
      (Quotient D.part × Fin (coherentPaddingSize A)))
    (hBPart : ∀ z w : Quotient D.part × Fin (coherentPaddingSize A),
      B.part z w ↔ z.1 = w.1)
    (hBOldF : ∀ a b : A, ¬D.part a b →
      B.F (D.factorialAuxiliaryOldMap j a)
        (D.factorialAuxiliaryOldMap j b) = D.F a b)
    (R : IndexedGauge s
      (Quotient D.part × Fin (coherentPaddingSize A))
      (Quotient B.part))
    (hRLabel : ∀ w : Quotient D.part × Fin (coherentPaddingSize A),
      R.label w = Quotient.mk B.part w)
    (hRF : ∀ x y : Quotient D.part × Fin (coherentPaddingSize A),
      ¬B.part x y → R.effective x y = B.F x y)
    (hRDiag : ∀ w : Quotient D.part × Fin (coherentPaddingSize A),
      R.vertexGauge w (R.label w) = 1)
    (K : EffectiveWitnessSkeleton B)
    (hK : ∀ i j : Quotient B.part, i ≠ j →
      K.colour (distinguishedWitnessPart B i)
        (distinguishedWitnessPart B j) = R.skeleton i j)
    (S : Set A) (p : S → A)
    (hp : Function.Injective p)
    (hE : ∀ a b : S, D.part a.val b.val ↔ D.part (p a) (p b))
    (hF : ∀ a b : S, ¬D.part a.val b.val →
      D.F (p a) (p b) = D.F a.val b.val) :
    ∃ theta : Equiv.Perm (EffectiveWitnessVertex B),
      (∀ a : S,
        theta (B.gaugeOldWitnessVertex R.vertexGauge
          (D.factorialAuxiliaryOldMap j a.val)) =
          B.gaugeOldWitnessVertex R.vertexGauge
            (D.factorialAuxiliaryOldMap j (p a))) ∧
      (∀ X Y : EffectiveWitnessVertex B,
        K.toEffectiveGeometry.part (theta X) (theta Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ X Y : EffectiveWitnessVertex B,
        ¬K.toEffectiveGeometry.part X Y →
          K.toEffectiveGeometry.F (theta X) (theta Y) =
            K.toEffectiveGeometry.F X Y) := by
  classical
  let W : Type _ := Quotient D.part × Fin (coherentPaddingSize A)
  let old : A → W := D.factorialAuxiliaryOldMap j
  let oldS : S → W := fun a => old a.val
  have hOldInj : Function.Injective oldS := by
    intro a b hab
    apply Subtype.ext
    exact hj (congrArg Prod.snd hab)
  let selected : Set W := Set.range oldS
  let pW : selected → W :=
    fun z => old (p (Classical.choose z.property))
  have hChoose (z : selected) :
      oldS (Classical.choose z.property) = z.val :=
    Classical.choose_spec z.property
  obtain ⟨iota, pi, hPiPart, hPiOld⟩ :=
    D.exists_factorialPartialLabelPermutations j hj S p hp hE
  have hPiSelected (z : selected) :
      pi z.val = pW z := by
    let a : S := Classical.choose z.property
    calc
      pi z.val = pi (old a.val) :=
        congrArg pi (hChoose z).symm
      _ = old (p a) := hPiOld a
      _ = pW z := rfl
  have hBPartOld (a b : A) :
      B.part (old a) (old b) ↔ D.part a b := by
    change B.part (Quotient.mk D.part a, j a)
      (Quotient.mk D.part b, j b) ↔ D.part a b
    exact (hBPart _ _).trans ⟨Quotient.exact, Quotient.sound⟩
  have hPWE (x y : selected) :
      B.part x.val y.val ↔ B.part (pW x) (pW y) := by
    let a : S := Classical.choose x.property
    let b : S := Classical.choose y.property
    have hx : x.val = old a.val := (hChoose x).symm
    have hy : y.val = old b.val := (hChoose y).symm
    rw [hx, hy]
    change B.part (old a.val) (old b.val) ↔
      B.part (old (p a)) (old (p b))
    exact (hBPartOld a.val b.val).trans
      ((hE a b).trans (hBPartOld (p a) (p b)).symm)
  have hPWF (x y : selected)
      (hxy : ¬B.part x.val y.val) :
      B.F (pW x) (pW y) = B.F x.val y.val := by
    let a : S := Classical.choose x.property
    let b : S := Classical.choose y.property
    have hx : x.val = old a.val := (hChoose x).symm
    have hy : y.val = old b.val := (hChoose y).symm
    have hab : ¬D.part a.val b.val := by
      intro he
      exact hxy (by rw [hx, hy]; exact (hBPartOld a.val b.val).mpr he)
    have hpab : ¬D.part (p a) (p b) := by
      intro he
      exact hab ((hE a b).mpr he)
    change B.F (old (p a)) (old (p b)) = B.F x.val y.val
    rw [hx, hy]
    calc
      B.F (old (p a)) (old (p b)) = D.F (p a) (p b) :=
        hBOldF (p a) (p b) hpab
      _ = D.F a.val b.val := hF a b hab
      _ = B.F (old a.val) (old b.val) :=
        (hBOldF a.val b.val hab).symm
  have hPos : 0 < coherentPaddingSize A := coherentPaddingSize_pos A
  let e : Quotient B.part ≃ Quotient D.part :=
    fixedFibreQuotientEquiv (coherentPaddingSize A) hPos B hBPart
  let iotaQ : Equiv.Perm (Quotient B.part) :=
    (e.trans iota).trans e.symm
  have hPiClass (z : W) :
      Quotient.mk B.part (pi z) =
        iotaQ (Quotient.mk B.part z) := by
    apply e.injective
    change (pi z).1 = iota z.1
    exact hPiPart z
  letI : Finite W := by infer_instance
  letI : Fintype (EffectiveWitnessPart B) :=
    B.fintypeEffectiveWitnessParts
  letI : LinearOrder (EffectiveWitnessPart B) :=
    LinearOrder.lift' (Fintype.equivFin (EffectiveWitnessPart B))
      (Fintype.equivFin (EffectiveWitnessPart B)).injective
  obtain ⟨theta, hThetaOld, hThetaE, hThetaF⟩ :=
    R.exists_effectivePartialConnector_onFixedGauge
      B hRLabel hRF hRDiag K hK selected pW
      hPWE hPWF iotaQ pi hPiClass hPiSelected
  refine ⟨theta, ?_, hThetaE, hThetaF⟩
  intro a
  let x : selected := ⟨old a.val, ⟨a, rfl⟩⟩
  calc
    theta (B.gaugeOldWitnessVertex R.vertexGauge (old a.val)) =
      B.gaugeOldWitnessVertex R.vertexGauge (pW x) :=
        hThetaOld x
    _ = B.gaugeOldWitnessVertex R.vertexGauge (pi (old a.val)) :=
      congrArg (B.gaugeOldWitnessVertex R.vertexGauge)
        (hPiSelected x).symm
    _ = B.gaugeOldWitnessVertex R.vertexGauge (old (p a)) :=
      congrArg (B.gaugeOldWitnessVertex R.vertexGauge) (hPiOld a)

end EffectiveGeometry

end SemigenericEPPA
