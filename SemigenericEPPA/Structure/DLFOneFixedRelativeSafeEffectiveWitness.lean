import SemigenericEPPA.Structure.DLFExplicitGoodSeedFixedRawCover
import SemigenericEPPA.Structure.DLFSelectedSafeFactorialEffectiveAction
import SemigenericEPPA.Valuations.FixedFactorialEffectivePartialConnector

/-!
# ONE finite effective DLF witness for ALL safe H actions and partial maps

Fix an arbitrary finite original raw R1--R3 structure Praw. Assume
only RawDatum.HasCompleteGoodOrbit: some one complete affine
congruence orbit, possibly a proper subset of the genuinely good
raw effective colours, lies inside the good set.

Select its seed g0 ONCE. The explicit-seed fixed factorial
construction then chooses j, Q, R, K and a joint raw cover J BEFORE
any old subset, any safe H-action or any partial map. A subsequent
safe action H≤Aut(Praw|S), even though it has no action on the
remainder Praw\S, extends homomorphically to the same full
two-layer effective witness. Every original partial raw
isomorphism separately extends to a full effective automorphism
of exactly the same K and zero-section.

The H-lift additionally certifies a COMPLETE good orbit for
every effective cross pair swapped by an H-involution, not merely
the existence of some reversal-fixed raw representative.

This is the global fixed EFFECTIVE relative safe EPPA package,
still prior to the regular-phase blowup and the noninvariant
raw B-colour cover.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Under ONE complete good congruence orbit, a fixed finite
two-layer effective witness carries every induced safe old group
action homomorphically AND extends every individual old partial
isomorphism on the SAME literal old embedding.

No global saturation, no reassignment of the seed g0 after H,
and no action of H on the whole of Praw. -/
theorem exists_oneFixedRelativeSafeEffectiveWitness
    (Praw : RawRectanglePresentation d A)
    (hGoodOrbit : d.HasCompleteGoodOrbit) :
    ∃ (g0 : G)
      (j : A → Fin (coherentPaddingSize A))
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
      let psi : A → EffectiveWitnessVertex B :=
        fun x => B.gaugeOldWitnessVertex R.vertexGauge (old x)
      ∃ J : FixedJointRawCover Praw K.toEffectiveGeometry psi,
        d.GoodCompleteOrbitAt g0 ∧
        Function.Injective psi ∧
        (∀ x y : A,
          K.toEffectiveGeometry.part (psi x) (psi y) ↔ Praw.part x y) ∧
        (∀ x y : A, ¬Praw.part x y →
          K.toEffectiveGeometry.F (psi x) (psi y) = D.F x y) ∧
        Finite (EffectiveWitnessVertex B) ∧
        (∀ (H : Type t) [Group H] (S : Set A)
          (rhoS : H →* Equiv.Perm S),
          (∀ (h : H) (a b : S),
            Praw.part (rhoS h a).val (rhoS h b).val ↔
              Praw.part a.val b.val) →
          (∀ (h : H) (a b : S),
            Praw.colour (rhoS h a).val (rhoS h b).val =
              Praw.colour a.val b.val) →
          (∀ (h : H), h * h = 1 →
            ∀ (a b : S), ¬Praw.part a.val b.val →
              rhoS h a = b → rhoS h b = a →
                d.GoodCompleteOrbitAt (D.F a.val b.val)) →
          ∃ Theta : H →* Equiv.Perm (EffectiveWitnessVertex B),
            (∀ (h : H) (a : S),
              Theta h (psi a.val) = psi (rhoS h a).val) ∧
            (∀ (h : H) (X Y : EffectiveWitnessVertex B),
              K.toEffectiveGeometry.part (Theta h X) (Theta h Y) ↔
                K.toEffectiveGeometry.part X Y) ∧
            (∀ (h : H) (X Y : EffectiveWitnessVertex B),
              ¬K.toEffectiveGeometry.part X Y →
                K.toEffectiveGeometry.F (Theta h X) (Theta h Y) =
                  K.toEffectiveGeometry.F X Y) ∧
            (∀ (h : H), h * h = 1 →
              ∀ (X Y : EffectiveWitnessVertex B),
                ¬K.toEffectiveGeometry.part X Y →
                  Theta h X = Y → Theta h Y = X →
                    d.GoodCompleteOrbitAt (K.toEffectiveGeometry.F X Y))) ∧
        (∀ (T : Set A) (p : T → A),
          Function.Injective p →
          (∀ x y : T,
            Praw.part x.val y.val ↔ Praw.part (p x) (p y)) →
          (∀ x y : T,
            Praw.colour (p x) (p y) = Praw.colour x.val y.val) →
          ∃ theta : Equiv.Perm (EffectiveWitnessVertex B),
            (∀ x : T, theta (psi x.val) = psi (p x)) ∧
            (∀ X Y : EffectiveWitnessVertex B,
              K.toEffectiveGeometry.part (theta X) (theta Y) ↔
                K.toEffectiveGeometry.part X Y) ∧
            (∀ X Y : EffectiveWitnessVertex B,
              ¬K.toEffectiveGeometry.part X Y →
                K.toEffectiveGeometry.F (theta X) (theta Y) =
                  K.toEffectiveGeometry.F X Y)) := by
  classical
  obtain ⟨g0, hg0, hOrbit⟩ := hGoodOrbit
  obtain ⟨j, Q, R, K, J, hj, _hQLabel,
      hBPart, hRLabel, hRConst, hRDiag, hRF, hKConst,
      _hBaseE, hBaseF, hPsiInj, hPsiPart, hPsiF, hFinite⟩ :=
    Praw.exists_fixedGoodSelectedRawLiftData_of_seed g0 hg0
  let D : EffectiveGeometry d.s A := Praw.effectiveReduct
  let B := Q.toEffectiveGeometry
  let old : A → Quotient D.part × Fin (coherentPaddingSize A) :=
    D.factorialAuxiliaryOldMap j
  let psi : A → EffectiveWitnessVertex B :=
    fun x => B.gaugeOldWitnessVertex R.vertexGauge (old x)
  have hKOld (i k : Quotient B.part) (_ : i ≠ k) :
      K.colour (distinguishedWitnessPart B i)
        (distinguishedWitnessPart B k) = R.skeleton i k :=
    (hKConst _ _).trans (hRConst i k).symm
  refine ⟨g0, j, Q, R, K, J, hOrbit,
    hPsiInj, hPsiPart, hPsiF, hFinite, ?_, ?_⟩
  · intro H _ S rhoS hPart hColour hOldSafe
    exact Praw.exists_selectedSafeEffectiveAction_onFixedSeedGauge
      g0 hOrbit j hj B hBPart hBaseF R hRLabel hRF
      hRConst hRDiag K hKConst
      S rhoS hPart hColour hOldSafe
  · intro T p hp hPart hColour
    have hEffE : ∀ x y : T,
        D.part x.val y.val ↔ D.part (p x) (p y) := by
      intro x y
      exact (Praw.effectiveReduct_part x.val y.val).trans
        ((hPart x y).trans
          (Praw.effectiveReduct_part (p x) (p y)).symm)
    have hEffF : ∀ x y : T, ¬D.part x.val y.val →
        D.F (p x) (p y) = D.F x.val y.val := by
      intro x y hxy
      have hOrig : ¬Praw.part x.val y.val := by
        intro hp'
        exact hxy ((Praw.effectiveReduct_part x.val y.val).mpr hp')
      have hNew : ¬Praw.part (p x) (p y) := by
        intro hp'
        exact hOrig ((hPart x y).mpr hp')
      exact Praw.effectiveReduct_equalColour
        (p x) (p y) x.val y.val (hColour x y) hNew
    exact D.exists_fixedFactorialEffectivePartialConnector
      j hj B hBPart hBaseF R hRLabel hRF hRDiag
      K hKOld T p hp hEffE hEffF

end RawRectanglePresentation

end SemigenericEPPA
