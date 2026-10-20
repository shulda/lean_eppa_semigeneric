import SemigenericEPPA.Bridge.CoherentGadgetClassificationNecessity
import Mathlib.Data.Fintype.Prod

/-!
# Coherent EPPA of the finite raw class: the necessary classification

The genuine 2+1 and 3+1 obstruction gadgets have finite old vertex
types Option Bool and Option (Option Bool), respectively.

Consequently if EVERY finite raw rectangle presentation in the
original literal binary language admits a typed coherent EPPA
witness, then both obstruction-gadget families necessarily have
such witnesses. Combining the two certified gadget implications
proves the human-facing NECESSARY classification condition:

  G is trivial  OR
  (there is a self-reversing raw colour AND all of its effective
   congruence orbit companions also have self-reversing raw colours).

The conclusion does not assume finiteness of the effective group
or the alphabet: it only assumes the stated finite-class coherent
EPPA property. The converse in the nontrivial G sector is separate
and not claimed here.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}

/-- The exact negative necessary condition follows from coherent
EPPA for EVERY finite raw rectangle presentation in the original
typed R1--R3 language. The witness W may depend on P and need not
have any fixed size. Testing only the 2+1 and 3+1 old structures
already forces the same algebraic conclusion. -/
theorem RawDatum.necessaryCoherentCondition_of_allFiniteRawPresentations
    (d : RawDatum G C)
    (hEPPA : ∀ (V : Type) [Fintype V]
        (P : RawRectanglePresentation d V),
        ∃ (W : Type w)
          (Q : RawRectanglePresentation d W)
          (ψ : Structure.Embedding (rectangleTrivialAction C)
            P.toStructure Q.toStructure),
          Structure.IsCoherentEPPAWitness (rectangleTrivialAction C) ψ) :
    Subsingleton G ∨
      (d.selfReverseEffective.Nonempty ∧ d.IsCongruenceSaturated) := by
  classical
  apply d.necessaryCoherentCondition_of_gadgetWitnesses
  · intro c hfix
    exact hEPPA (Option Bool) (d.twoPlusOneRawPresentation c)
  · intro col
    exact hEPPA (Option (Option Bool)) (d.threePlusOneRawPresentation col)

end SemigenericEPPA
