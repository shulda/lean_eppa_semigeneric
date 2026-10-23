import SemigenericEPPA.Bridge.SwappedDifferentOldIndexMiddle
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport

/-!
# One complete good orbit for an actual swapped valuation pair

The certified positive coherent common-middle calculation is
strictly stronger than its global saturation conclusion:
F_old(a,b) = s(aOld)*middle*aOld and
F_witness(X,Y) = s(aNew)*middle*aNew.
They are related by the exact original affine congruence action.
Consequently an OLD pair in one complete good orbit forces the
NEW genuinely swapped witness colour into that same orbit,
without making any assertion about other good colours.

This works in arbitrary nonabelian G, including s(1)≠1.
The complete actual-witness action and old row equations remain
identical to the certified coherent common-middle proof. It is a
local safety bridge, not yet a relative EPPA witness or a DLF
classification.
-/

namespace SemigenericEPPA

universe u v w t z
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {C : Type w} {V : Type t}
variable {d : RawDatum G C}

/-- The exact swapped-witness common-middle calculation transfers
the chosen old complete good orbit to the actual new witness edge. -/
theorem RawDatum.completeGoodOrbitAt_of_swappedWitness_projectedOldMiddle
    (d : RawDatum G C)
    (D : EffectiveGeometry d.s V)
    (P : IndexedGauge d.s V (Quotient D.part))
    (hPLabel : ∀ x : V,
      P.label x = Quotient.mk D.part x)
    (g0 : G)
    (hConstant : ∀ i j : Quotient D.part,
      P.skeleton i j = g0)
    (hColour : ∀ x y : V, ¬D.part x y →
      P.effective x y = D.F x y)
    (pi : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (pi h x) =
        iota h (Quotient.mk D.part x))
    (M : H → Quotient D.part → Quotient D.part → G)
    (K : EffectiveWitnessSkeleton D)
    (hK : ∀ q r : EffectiveWitnessPart D,
      K.colour q r = g0)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (h : H) (X Y : EffectiveWitnessVertex D)
    (hXY : X.part ≠ Y.part)
    (hSwapX : witnessCocyclePerm D sigma pi hcompat
        (fun k q r => M k q.1 r.1) h X = Y)
    (hSwapY : witnessCocyclePerm D sigma pi hcompat
        (fun k q r => M k q.1 r.1) h Y = X)
    (a b : V)
    (hab : ¬D.part a b)
    (hIndexA : X.part.1 = Quotient.mk D.part a)
    (hIndexB : Y.part.1 = Quotient.mk D.part b)
    (hOldSwapA : pi h a = b)
    (hOldSwapB : pi h b = a)
    (hOldRow :
      P.vertexGauge (pi h a)
          (iota h (Quotient.mk D.part b)) =
        M h (Quotient.mk D.part a) (Quotient.mk D.part b) *
          P.vertexGauge a (Quotient.mk D.part b))
    (hOldSafe : d.GoodCompleteOrbitAt (D.F a b)) :
    ∃ aNew aOld middle : G,
      K.toEffectiveGeometry.F X Y =
        d.s aNew * middle * aNew ∧
      D.F a b = d.s aOld * middle * aOld ∧
      d.GoodCompleteOrbitAt (K.toEffectiveGeometry.F X Y) := by
  let i : Quotient D.part := Quotient.mk D.part a
  let j : Quotient D.part := Quotient.mk D.part b
  let aOld : G := P.vertexGauge a j
  let aNew : G := X.crossIncidence Y.part hXY.symm
  let middle : G := g0⁻¹ * M h i j
  have hTarget : iota h j = i := by
    calc
      iota h j = Quotient.mk D.part (pi h b) := (hcls h b).symm
      _ = i := congrArg (Quotient.mk D.part) hOldSwapB
  have hRowActual : P.vertexGauge b i = M h i j * aOld := by
    have hr := hOldRow
    rw [hOldSwapA, hTarget] at hr
    exact hr
  have hPneq : P.label a ≠ P.label b := by
    rw [hPLabel a, hPLabel b]
    intro heq
    exact hab (Quotient.exact heq)
  have hOldFormula : D.F a b =
      d.s aOld * middle * aOld := by
    have hP := P.effective_cross a b hPneq
    rw [hPLabel a, hPLabel b, hConstant i j,
      hRowActual] at hP
    unfold gaugeColour at hP
    calc
      D.F a b = P.effective a b := (hColour a b hab).symm
      _ = d.s aOld * middle * aOld := by
        simpa only [aOld, middle, i, j, mul_assoc] using hP
  have hNewFormula : K.toEffectiveGeometry.F X Y =
      d.s aNew * middle * aNew := by
    have hf := witnessCocyclePerm_swapped_crossColour
      D K sigma pi hcompat (fun k q r => M k q.1 r.1)
        h X Y hXY hSwapX hSwapY
    rw [hK X.part Y.part, hIndexA, hIndexB] at hf
    simpa only [aNew, middle, i, j] using hf
  have hGoodOldMiddle :
      d.GoodCompleteOrbitAt (d.s aOld * middle * aOld) := by
    rw [← hOldFormula]
    exact hOldSafe
  have hGoodNew :
      d.GoodCompleteOrbitAt (K.toEffectiveGeometry.F X Y) := by
    rw [hNewFormula]
    rw [← congruence_commonGaugeMiddle d.s aNew aOld middle]
    exact d.goodCompleteOrbitAt_congruence
      (d.s aOld * middle * aOld)
      (d.s aNew * (d.s aOld)⁻¹) hGoodOldMiddle
  exact ⟨aNew, aOld, middle,
    hNewFormula, hOldFormula, hGoodNew⟩


end SemigenericEPPA
