import SemigenericEPPA.Valuations.WitnessCocycleAction
import SemigenericEPPA.Algebra.AffineCongruenceGaugeMiddle

/-!
# Actual swapped-witness effective colour has one gauge middle

Equation (4.29) of the coherent-positive manuscript is a consequence
of the REAL witness-coordinate permutation, not a separate assumption.
For an arbitrary H-element which swaps two witness vertices X and Y
in distinct witness parts, the transported cross-incidence on the
swapped edge is exactly m_h(q,r) times the old cross-incidence.

In an arbitrary affine and noncommutative gauge with skeleton K,
the resulting effective colour is
  s(a) * (K(q,r)^(-1) * m_h(q,r)) * a,
where a is the genuine incidence of X towards the target part r.
When K(q,r)=1 this specializes to manuscript (4.29), s(a)*m*a.

This exact factorization is the witness-side input to the
previously verified common-middle congruence-orbit safety theorem.
It works for elements of any order. No group cocycle or full
automorphism-preservation assumption is needed for this calculation.
-/

namespace SemigenericEPPA

universe u v w

variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {s : AffineAntiInvolution G}

/-- A genuinely swapped cross-part witness edge has the exact
noncommutative affine common-middle normal form, extracted from
the actual witness permutation and its coordinate-transport law.
The multiplication order K^(-1) * m is essential. -/
theorem witnessCocyclePerm_swapped_crossColour
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (h : H) (X Y : EffectiveWitnessVertex D)
    (hXY : X.part ≠ Y.part)
    (hSwapX : witnessCocyclePerm D sigma pi hcompat m h X = Y)
    (hSwapY : witnessCocyclePerm D sigma pi hcompat m h Y = X) :
    K.toEffectiveGeometry.F X Y =
      s (X.crossIncidence Y.part hXY.symm) *
        ((K.colour X.part Y.part)⁻¹ * m h X.part Y.part) *
          X.crossIncidence Y.part hXY.symm := by
  have hIndex : sigma h Y.part = X.part := by
    have hpart :=
      witnessCocyclePerm_part D sigma pi hcompat m h Y
    rw [hSwapY] at hpart
    exact hpart.symm
  have hInc :
      Y.crossIncidence X.part hXY =
        m h X.part Y.part * X.crossIncidence Y.part hXY.symm := by
    have ht :=
      witnessCocyclePerm_incidence D sigma pi hcompat m
        h X Y.part hXY.symm
    simpa only [hSwapX, hIndex] using ht
  rw [K.witness_cross_colour X Y hXY]
  rw [hInc]
  unfold gaugeColour
  group

/-- In particular, on a cross edge whose skeleton is 1, this
is EXACTLY manuscript equation (4.29), without an assumption
that the affine reversal maps 1 to 1. -/
theorem witnessCocyclePerm_swapped_crossColour_oneSkeleton
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (h : H) (X Y : EffectiveWitnessVertex D)
    (hXY : X.part ≠ Y.part)
    (hK : K.colour X.part Y.part = 1)
    (hSwapX : witnessCocyclePerm D sigma pi hcompat m h X = Y)
    (hSwapY : witnessCocyclePerm D sigma pi hcompat m h Y = X) :
    K.toEffectiveGeometry.F X Y =
      s (X.crossIncidence Y.part hXY.symm) *
        m h X.part Y.part *
          X.crossIncidence Y.part hXY.symm := by
  rw [witnessCocyclePerm_swapped_crossColour
    D K sigma pi hcompat m h X Y hXY hSwapX hSwapY, hK]
  group

end SemigenericEPPA
