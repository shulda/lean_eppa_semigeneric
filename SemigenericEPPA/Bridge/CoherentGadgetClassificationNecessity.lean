import SemigenericEPPA.Bridge.TwoPlusOneCoherentOrbitSaturation
import SemigenericEPPA.Bridge.ThreePlusOneCoherentNoGoodObstruction

/-!
# Necessary condition for the coherent-EPPA classification

The actual old 2+1 gadget forces congruence saturation of the set of
effective fibres containing a self-reversing raw colour. This holds
even if the set is empty.

The actual old 3+1 gadget with one asymmetric effective colour
δ ≠ 1 forces that set to be NONEMPTY whenever G is nontrivial.

Combining these two genuinely typed coherent-EPPA obstructions gives
the precise necessary side of the mathematical classification:

    G is trivial
      OR
    (S is nonempty AND S is congruence-saturated).

Only coherent witnesses for these TWO explicit families of old raw
structures are assumed; no full EPPA class hypothesis or arbitrary
whole-witness involutions are supplied. Those involutions have
already been derived from upstream CoherentTriple laws.

The converse (coherent positive construction for nontrivial G with
nonempty saturated S) remains a separate target.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}

/-- Coherent witnesses for every actual old 2+1 and 3+1 test
structure force exactly the nontrivial-G negative classification
condition: either G has one element, or S is nonempty and
congruence-saturated. No finiteness or HKN assumptions are used. -/
theorem RawDatum.necessaryCoherentCondition_of_gadgetWitnesses
    (d : RawDatum G C)
    (hTwo : ∀ (c : Bool → C)
        (hfix : d.reverse (c false) = c false),
        ∃ (W : Type w)
          (Q : RawRectanglePresentation d W)
          (ψ : Structure.Embedding (rectangleTrivialAction C)
            (d.twoPlusOneRawPresentation c).toStructure Q.toStructure),
          Structure.IsCoherentEPPAWitness (rectangleTrivialAction C) ψ)
    (hThree : ∀ (col : Option Bool → C),
        ∃ (W : Type w)
          (Q : RawRectanglePresentation d W)
          (ψ : Structure.Embedding (rectangleTrivialAction C)
            (d.threePlusOneRawPresentation col).toStructure Q.toStructure),
          Structure.IsCoherentEPPAWitness (rectangleTrivialAction C) ψ) :
    Subsingleton G ∨
      (d.selfReverseEffective.Nonempty ∧ d.IsCongruenceSaturated) := by
  classical
  have hsat : d.IsCongruenceSaturated :=
    d.isCongruenceSaturated_of_twoPlusOneCoherentWitnesses hTwo
  by_cases htriv : ∀ a : G, a = 1
  · left
    exact ⟨fun a b => (htriv a).trans (htriv b).symm⟩
  · right
    obtain ⟨delta, hdelta⟩ := not_forall.mp htriv
    exact ⟨d.goodNonempty_of_threePlusOneCoherentWitnesses
      delta hdelta hThree, hsat⟩

end SemigenericEPPA
