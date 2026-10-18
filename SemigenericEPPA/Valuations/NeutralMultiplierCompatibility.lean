import SemigenericEPPA.Valuations.TwistedPartPermutation
import SemigenericEPPA.Valuations.WitnessSkeleton
import SemigenericEPPA.Algebra.PartialGaugeFamilies

/-!
# Neutral witnessed parts and compatibility of prescribed multipliers

The source parts on which manuscript (3.19) prescribes multipliers
are exactly the *neutral* witness parts indexed by E-classes visited
by the old partial domain.  The compatibility equation for these
parts follows directly from the old (3.15) identity and the exact
neutral-to-neutral skeleton equation (3.4).

Importantly, a pair of DISTINCT neutral witness parts has distinct
underlying old E-class indices: we must not silently assume this for
arbitrary blown-up witness parts with the same old index.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- A neutral part over an old E-class that is visited by the
domain of the old partial automorphism. -/
def IsVisitedNeutralPart
    (D : EffectiveGeometry s V)
    (visited : Quotient D.part → Prop)
    (q : EffectiveWitnessPart D) : Prop :=
  visited q.1 ∧ q.2 = neutralPartValuation

/-- Equation (3.19): prescribed witness-part multipliers depend only
on the underlying old E-class indices, not on the target valuation. -/
def neutralPrescribedMultiplier
    (D : EffectiveGeometry s V)
    (m : Quotient D.part → Quotient D.part → G)
    (q r : EffectiveWitnessPart D) : G :=
  m q.1 r.1

/-- All pairwise compatibility equations required by the
constrained witness-automorphism construction follow from
(3.15) on visited E-classes, provided the twists are trivial
on those source classes.

This handles arbitrary noncommutative G and affine reversal s. -/
theorem neutralPrescribedMultiplier_compatible
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (hK : K.ExtendsOldSkeleton D)
    (ι : Equiv.Perm (Quotient D.part))
    (π : Equiv.Perm V)
    (L : Quotient D.part → V → G)
    (visited : Quotient D.part → Prop)
    (hL : ∀ j, visited j → ∀ x, L j x = 1)
    (m : Quotient D.part → Quotient D.part → G)
    (hm : ∀ i j, visited i → visited j → i ≠ j →
      s.normalized (m i j) *
          (D.toQuotientGauge.skeleton (ι i) (ι j))⁻¹ *
            m j i =
        (D.toQuotientGauge.skeleton i j)⁻¹)
    (q r : EffectiveWitnessPart D)
    (hq : IsVisitedNeutralPart D visited q)
    (hr : IsVisitedNeutralPart D visited r)
    (hqr : q ≠ r) :
    s.normalized (neutralPrescribedMultiplier D m q r) *
        (K.colour
          (twistedWitnessPartPerm D ι π L q)
          (twistedWitnessPartPerm D ι π L r))⁻¹ *
          neutralPrescribedMultiplier D m r q =
      (K.colour q r)⁻¹ := by
  have hij : q.1 ≠ r.1 := by
    intro heq
    apply hqr
    apply Prod.ext
    · exact heq
    · exact hq.2.trans hr.2.symm
  have hqe : q = distinguishedWitnessPart D q.1 := by
    apply Prod.ext
    · rfl
    · exact hq.2
  have hre : r = distinguishedWitnessPart D r.1 := by
    apply Prod.ext
    · rfl
    · exact hr.2
  have hsq :
      twistedWitnessPartPerm D ι π L q =
        distinguishedWitnessPart D (ι q.1) := by
    conv_lhs => rw [hqe]
    exact twistedWitnessPartPerm_distinguished
      D ι π L q.1 (hL q.1 hq.1)
  have hsr :
      twistedWitnessPartPerm D ι π L r =
        distinguishedWitnessPart D (ι r.1) := by
    conv_lhs => rw [hre]
    exact twistedWitnessPartPerm_distinguished
      D ι π L r.1 (hL r.1 hr.1)
  have hKold :
      K.colour q r =
        D.toQuotientGauge.skeleton q.1 r.1 := by
    rw [hqe, hre]
    exact hK q.1 r.1 hij
  have hKnew :
      K.colour
          (twistedWitnessPartPerm D ι π L q)
          (twistedWitnessPartPerm D ι π L r) =
        D.toQuotientGauge.skeleton (ι q.1) (ι r.1) := by
    rw [hsq, hsr]
    exact hK (ι q.1) (ι r.1) (by
      intro h
      exact hij (ι.injective h))
  change s.normalized (m q.1 r.1) *
      (K.colour
        (twistedWitnessPartPerm D ι π L q)
        (twistedWitnessPartPerm D ι π L r))⁻¹ *
        m r.1 q.1 = (K.colour q r)⁻¹
  rw [hKnew, hKold]
  exact hm q.1 r.1 hq.1 hr.1 hij

end SemigenericEPPA
