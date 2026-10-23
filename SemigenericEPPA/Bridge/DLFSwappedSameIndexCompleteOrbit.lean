import SemigenericEPPA.Bridge.SwappedSameOldIndexGood
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport

/-!
# Same-original-index swapped witness edges lie in ONE good orbit

The exact genuine two-layer swapped-edge colour formula has
F(X,Y) = s(a) * g0⁻¹ * a whenever a witness action exchanges
two valuation parts with the same original E-index and its
diagonal multiplier equals 1.

Using the original affine anti-involution, we express every such
value as an explicit affine congruence translate of g0. Thus if
the orbit of g0 consists of genuinely self-reversing raw colours,
so does the entire orbit of the swapped witness colour.

Neither global saturation of the good set, any commutativity
assumption, nor s(1)=1 is needed. The true witness group action,
fibre compatibility and diagonal multiplier hypotheses are
identical to the certified coherent-EPPA same-index lemma.
-/

namespace SemigenericEPPA

universe u v w z
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {C : Type w} {V : Type z}

/-- Exact affine orbit identity for every same-old-index
swapped-witness colour, under only a single good orbit. -/
theorem RawDatum.sameIndexColour_completeGoodOrbit
    (d : RawDatum G C) (g0 : G)
    (hGoodOrbit : d.GoodCompleteOrbitAt g0)
    (a : G) :
    d.GoodCompleteOrbitAt (d.s a * g0⁻¹ * a) := by
  have hgGood := d.good_of_completeOrbitAt g0 hGoodOrbit
  have hgFixed : d.s g0 = g0 :=
    d.selfReverseEffective_subset_fixed hgGood
  let k : G :=
    (d.s a * (d.s 1)⁻¹) * (d.s 1 * g0⁻¹)
  have hEq :
      congruence d.s k g0 = d.s a * g0⁻¹ * a := by
    dsimp [k]
    rw [congruence_mul,
      congruence_inverse_fixed_skeleton_seed d.s g0 hgFixed]
    simpa only [mul_one] using
      (congruence_commonGaugeMiddle d.s a 1 g0⁻¹)
  rw [← hEq]
  exact d.goodCompleteOrbitAt_congruence g0 k hGoodOrbit

/-- Same-old-index swapped edges of an actual two-layer witness
are in one complete good orbit, not merely somewhere in the
good effective set. -/
theorem RawDatum.completeGoodOrbitAt_of_swappedWitness_sameOldIndex
    (d : RawDatum G C)
    (g0 : G) (hGoodOrbit : d.GoodCompleteOrbitAt g0)
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
    d.GoodCompleteOrbitAt (K.toEffectiveGeometry.F X Y) := by
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
  exact d.sameIndexColour_completeGoodOrbit g0 hGoodOrbit a

end SemigenericEPPA
