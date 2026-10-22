import SemigenericEPPA.Valuations.OneFixedFiniteGoodEffectiveWitness
import SemigenericEPPA.Structure.FixedJointRawCover
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge

/-!
# One finite fixed nontrivial-G effective witness AND its joint raw cover

The certified positive nontrivial-G effective construction provides
one finite factorial two-layer witness with constant genuinely good
skeleton K and a single literal old E/F embedding ψ. The same
witness supports strict extensions of the automorphism group of
EVERY induced effective old substructure, with no change to its
underlying carrier, K or ψ.

The independently certified fixed joint raw-cover theorem produces,
over ANY such finite E/F witness and a compatible old RAW
embedding, one finite residual code and one raw baseline BEFORE
any later partial map or H-action. This SAME raw cover has both:
* the original raw presentation as a literal induced zero-section;
* conditional ordinary partial-map and flip-safe group-action
  lift APIs, valid simultaneously for every later group H.

Here these existential choices are composed in the correct order.
No raw-colour cover is selected as a function of H or S.

The conclusion does NOT yet assert that every effective H-action
is raw flip-safe. That is a separate geometric theorem requiring
the factorial occupied projection and the two certified swapped
edge cases; nor does it assert the final typed coherent groupoid.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- For a finite original raw R1–R3 rectangle presentation with
at least one genuine good effective colour, fix ONE finite
effective witness, ONE literal old zero-section, and ONE finite
joint raw cover with its residual code and baseline. All selected
old H-actions have strict effective extensions on the same
witness; the cover retains its conditional homomorphic raw
lift API for all such actions.

The remaining geometric condition is the actual raw flip-safety
of these group actions; it is not smuggled into the hypotheses
or silently inferred from mere effective-colour preservation. -/
theorem exists_oneFixedGoodEffectiveWitness_andJointRawCover
    (P : RawRectanglePresentation d A)
    (hGood : d.selfReverseEffective.Nonempty) :
    ∃ (j : A → Fin (coherentPaddingSize A))
      (Q : IndexedGauge d.s
        (Quotient P.effectiveReduct.part × Fin (coherentPaddingSize A))
        (Quotient P.effectiveReduct.part))
      (R : IndexedGauge d.s
        (Quotient P.effectiveReduct.part × Fin (coherentPaddingSize A))
        (Quotient Q.toEffectiveGeometry.part))
      (K : EffectiveWitnessSkeleton Q.toEffectiveGeometry),
      let B := Q.toEffectiveGeometry
      let ψ : A → EffectiveWitnessVertex B :=
        fun x => B.gaugeOldWitnessVertex R.vertexGauge
          (P.effectiveReduct.factorialAuxiliaryOldMap j x)
      ∃ J : FixedJointRawCover P K.toEffectiveGeometry ψ,
        Function.Injective ψ ∧
        (∀ x y : A,
          K.toEffectiveGeometry.part (ψ x) (ψ y) ↔ P.part x y) ∧
        (∀ x y : A, ¬P.part x y →
          K.toEffectiveGeometry.F (ψ x) (ψ y) =
            P.effectiveReduct.F x y) ∧
        Finite (EffectiveWitnessVertex B) ∧
        (∀ (H : Type t) [Group H]
          (S : Set A) (ρ : H →* Equiv.Perm S),
          (∀ (h : H) (x y : S),
            P.part (ρ h x).val (ρ h y).val ↔ P.part x.val y.val) →
          (∀ (h : H) (x y : S), ¬P.part x.val y.val →
            P.effectiveReduct.F (ρ h x).val (ρ h y).val =
              P.effectiveReduct.F x.val y.val) →
          ∃ Θ : H →* Equiv.Perm (EffectiveWitnessVertex B),
            (∀ (h : H) (x : S),
              Θ h (ψ x.val) = ψ (ρ h x).val) ∧
            (∀ (h : H) (X Y : EffectiveWitnessVertex B),
              K.toEffectiveGeometry.part (Θ h X) (Θ h Y) ↔
                K.toEffectiveGeometry.part X Y) ∧
            (∀ (h : H) (X Y : EffectiveWitnessVertex B),
              ¬K.toEffectiveGeometry.part X Y →
                K.toEffectiveGeometry.F (Θ h X) (Θ h Y) =
                  K.toEffectiveGeometry.F X Y)) := by
  classical
  let D : EffectiveGeometry d.s A := P.effectiveReduct
  have hSame (x y : A) (hxy : D.part x y) :
      D.F x y = 1 := by
    change P.toStructure_isRectangleStructure.effectiveTotal x y = 1
    exact P.toStructure_isRectangleStructure.effectiveTotal_same
      x y hxy
  obtain ⟨j, Q, R, K, hInj, hE, hF, hFinite, hGroups⟩ :=
    D.exists_oneFiniteGoodEffectiveWitness_allRelativeGroupActions
      hSame hGood
  let B : EffectiveGeometry d.s
      (Quotient D.part × Fin (coherentPaddingSize A)) :=
    Q.toEffectiveGeometry
  let ψ : A → EffectiveWitnessVertex B :=
    fun x => B.gaugeOldWitnessVertex R.vertexGauge
      (D.factorialAuxiliaryOldMap j x)
  have hRawPart (x y : A) :
      K.toEffectiveGeometry.part (ψ x) (ψ y) ↔
        P.part x y :=
    (hE x y).trans (P.effectiveReduct_part x y)
  have hRawPhi (x y : A) (c : C)
      (hc : P.colour x y = some c) :
      d.phi c = K.toEffectiveGeometry.F (ψ x) (ψ y) := by
    have hxy : ¬D.part x y := by
      intro hp
      have hn : P.colour x y = none :=
        (P.colour_none_iff x y).2 hp
      rw [hc] at hn
      cases hn
    calc
      d.phi c = D.F x y :=
        P.effectiveReduct_crossColour x y c hc
      _ = K.toEffectiveGeometry.F (ψ x) (ψ y) :=
        (hF x y hxy).symm
  letI : Finite (EffectiveWitnessVertex B) := hFinite
  obtain ⟨J⟩ :=
    exists_fixedJointRawCover P K.toEffectiveGeometry
      ψ hInj hRawPart hRawPhi
  have hRawF (x y : A) (hxy : ¬P.part x y) :
      K.toEffectiveGeometry.F (ψ x) (ψ y) = D.F x y :=
    hF x y hxy
  have hRawGroups : ∀ (H : Type t) [Group H]
      (S : Set A) (ρ : H →* Equiv.Perm S),
      (∀ (h : H) (x y : S),
        P.part (ρ h x).val (ρ h y).val ↔ P.part x.val y.val) →
      (∀ (h : H) (x y : S), ¬P.part x.val y.val →
        D.F (ρ h x).val (ρ h y).val = D.F x.val y.val) →
      ∃ Θ : H →* Equiv.Perm (EffectiveWitnessVertex B),
        (∀ (h : H) (x : S),
          Θ h (ψ x.val) = ψ (ρ h x).val) ∧
        (∀ (h : H) (X Y : EffectiveWitnessVertex B),
          K.toEffectiveGeometry.part (Θ h X) (Θ h Y) ↔
            K.toEffectiveGeometry.part X Y) ∧
        (∀ (h : H) (X Y : EffectiveWitnessVertex B),
          ¬K.toEffectiveGeometry.part X Y →
            K.toEffectiveGeometry.F (Θ h X) (Θ h Y) =
              K.toEffectiveGeometry.F X Y) := by
    intro H _ S ρ hPart hEff
    apply hGroups H S ρ
    · intro h x y
      exact (P.effectiveReduct_part _ _).trans
        ((hPart h x y).trans (P.effectiveReduct_part _ _).symm)
    · intro h x y hxy
      apply hEff h x y
      exact hxy
  exact ⟨j, Q, R, K, J, hInj,
    hRawPart, hRawF, hFinite, hRawGroups⟩

end RawRectanglePresentation

end SemigenericEPPA
