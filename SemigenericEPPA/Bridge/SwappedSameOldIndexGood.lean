import SemigenericEPPA.Valuations.SwappedWitnessGaugeMiddle
import SemigenericEPPA.Algebra.GoodDefaultSkeletonOrbit

/-!
# Genuine swapped same-old-index witness edges are raw flip-safe

This is the first complete (not merely abstract-orbit) branch of the
nontrivial-G positive coherent flip-safety calculation.

On a real two-layer valuation witness with one fixed skeleton g0
from the genuine good raw effective colours, suppose the canonical
multipliers depend only on original E-indices and equal 1 whenever
the two source/target index coordinates coincide.

If some group element h actually exchanges two witness vertices X,Y
in DISTINCT witness valuation parts but with the SAME ORIGINAL
E-index, then the verified coordinate transport gives exactly

    F(X,Y) = s(a) * g0^(-1) * a

where a is X's genuine incidence towards Y's part. The independent
affine-congruence safety theorem says this is in the good raw set,
provided the good effective-colour set is congruence-saturated.

This works with arbitrary nonabelian G and affine anti-involution,
including s(1)≠1. No restriction on the order of h, and no false
assumption that different valuation parts have different old
E-indices. The different-old-index branch separately needs the
equivariant projection onto actually swapped vertices of old S.
-/

namespace SemigenericEPPA

universe u v w z

variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {C : Type w} {V : Type z}

/-- Every ACTUALLY exchanged witness cross-edge with a common old
E-class index is raw flip-safe under the coherent-positive global
congruence-saturation hypothesis, for the same constant-good
skeleton selected before H. -/
theorem RawDatum.good_of_swappedWitness_sameOldIndex
    (d : RawDatum G C)
    (hsat : d.IsCongruenceSaturated)
    (g0 : G) (hGood : g0 ∈ d.selfReverseEffective)
    (D : EffectiveGeometry d.s V)
    (K : EffectiveWitnessSkeleton D)
    (hK : ∀ q r : EffectiveWitnessPart D,
      K.colour q r = g0)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (hmDiag : ∀ (h : H) (q r : EffectiveWitnessPart D),
      q.1 = r.1 → m h q r = 1)
    (h : H) (X Y : EffectiveWitnessVertex D)
    (hXY : X.part ≠ Y.part)
    (hSame : X.part.1 = Y.part.1)
    (hSwapX : witnessCocyclePerm D sigma pi hcompat m h X = Y)
    (hSwapY : witnessCocyclePerm D sigma pi hcompat m h Y = X) :
    K.toEffectiveGeometry.F X Y ∈ d.selfReverseEffective := by
  let a : G := X.crossIncidence Y.part hXY.symm
  have hskeleton : K.colour X.part Y.part = g0 :=
    hK X.part Y.part
  have hm : m h X.part Y.part = 1 :=
    hmDiag h X.part Y.part hSame
  have hformula :=
    witnessCocyclePerm_swapped_crossColour
      D K sigma pi hcompat m h X Y hXY hSwapX hSwapY
  have hcolour :
      K.toEffectiveGeometry.F X Y = d.s a * g0⁻¹ * a := by
    rw [hskeleton, hm] at hformula
    calc
      K.toEffectiveGeometry.F X Y =
          d.s a * (g0⁻¹ * 1) * a := hformula
      _ = d.s a * g0⁻¹ * a := by group
  rw [hcolour]
  exact d.good_swappedSameIndex_of_saturated
    hsat g0 hGood a

end SemigenericEPPA
