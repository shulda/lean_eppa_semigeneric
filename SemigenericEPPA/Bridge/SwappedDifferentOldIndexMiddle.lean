import SemigenericEPPA.Valuations.SwappedWitnessGaugeMiddle
import SemigenericEPPA.Algebra.AffineCongruenceGaugeMiddle
import SemigenericEPPA.Structure.IndexedGauge

/-!
# Different-old-index swapped witness and genuine old edges share a middle

The main nontrivial-G coherent-EPPA raw flip-safety proof divides
swapped cross-witness pairs into two branches:
* equal original old E-indices (already certified);
* different original E-indices, where the endpoints of the
  fixed-carrier auxiliary action project equivariantly to a
  genuinely swapped pair of selected old vertices.

Here the latter algebraic step is proved for the REAL two-layer
valuation witness permutation. Let g0 be the globally chosen
constant affine-reversal-fixed skeleton and M_h(i,j) the canonical
selected-substructure multiplier. If an old selected pair a,b
satisfies h(a)=b,h(b)=a, then its transported old gauge row gives
  a(b,i) = M_h(i,j) a(a,j),
where i=[a],j=[b]. Its true effective old colour therefore is
  s(aOld) * (g0^-1 * M_h(i,j)) * aOld.

For any actual cross-witness pair X,Y exchanged by the same
group element, with original old indices i,j and incidence aNew,
the verified genuine witness transport formula gives
  F_new(X,Y) = s(aNew) * (g0^-1 * M_h(i,j)) * aNew.

Thus both colours share EXACTLY one noncommutative affine gauge
middle. Global congruence saturation transports the old good
raw colour to the witness edge. No s(1)=1, abelianness, recentering,
or requirement that h is an involution is used.

The geometric projection guaranteeing the old a,b exist and
are swapped is deliberately separate. This is precisely the
swapped-only common-middle input for that final projection lemma.
-/

namespace SemigenericEPPA

universe u v w t z

variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {C : Type w} {V : Type t}
variable {d : RawDatum G C}

/-- Actual old-index different-branch flip safety from the exact
common affine middle of the old projected edge and a genuinely
swapped valuation-witness edge.

The old selected pair a,b is supplied with its real swap equations
and ONE selected old gauge-row equation. No old colour invariance
outside that selected pair is assumed.

The witness action is the genuine coordinate permutation, not an
arbitrary colour-preserving permutation with unspecified incidence.
-/
theorem RawDatum.good_of_swappedWitness_projectedOldMiddle
    (d : RawDatum G C)
    (hsat : d.IsCongruenceSaturated)
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
    (hOldGood : D.F a b ∈ d.selfReverseEffective) :
    ∃ aNew aOld middle : G,
      K.toEffectiveGeometry.F X Y =
        d.s aNew * middle * aNew ∧
      D.F a b = d.s aOld * middle * aOld ∧
      K.toEffectiveGeometry.F X Y ∈ d.selfReverseEffective := by
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
      d.s aOld * middle * aOld ∈ d.selfReverseEffective := by
    rw [← hOldFormula]
    exact hOldGood
  have hGoodNew :
      K.toEffectiveGeometry.F X Y ∈ d.selfReverseEffective := by
    rw [hNewFormula]
    exact d.goodGaugeMiddle_of_saturated
      hsat aNew aOld middle hGoodOldMiddle
  exact ⟨aNew, aOld, middle,
    hNewFormula, hOldFormula, hGoodNew⟩

end SemigenericEPPA
