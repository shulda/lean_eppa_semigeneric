import SemigenericEPPA.Structure.DLFRelationalClassification
import SemigenericEPPA.Bridge.FiniteCanonicalUniverseCoherentClassification
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# A concrete four-element separation: DLF but NOT coherent EPPA

Take the cyclic group C₄ in multiplicative notation, the
IDENTITY affine anti-involution (valid because C₄ is abelian),
and five raw colours. Four of them map onto the four effective
colours; a fifth is a second raw representative of effective
colour 3. The raw reversal fixes the first three colours and
exchanges the two representatives of 3.

Hence S, the set of effective fibres containing self-reversing
raw representatives, is exactly {0,1,2}. The congruence orbits
for s=id are {0,2} and {1,3}: one entire orbit is good but the
good set is not globally saturated.

We use the CI-certified classification theorems to conclude
DLF for the actual original relational Fraisse age, while
coherent EPPA FAILS for the same original relational class.
This is an explicit data-level example rather than an abstract
algebraic condition without an exhibited raw palette.
-/

namespace SemigenericEPPA

namespace FourColourSeparation

/-- The four-element cyclic effective group, written
multiplicatively to match the general noncommutative API. -/
abbrev G4 := Multiplicative (ZMod 4)

/-- The identity on an abelian group is a legitimate affine
anti-involution in the article's precise convention. -/
def identityReversal : AffineAntiInvolution G4 where
  toFun := id
  involutive := by intro g; rfl
  map_mul := by
    intro x y
    simpa using (mul_comm x y)

/-- The raw reversal fixes 0,1,2 and exchanges 3 and 4. -/
def rawReverse (c : Fin 5) : Fin 5 :=
  if c = 3 then 4 else if c = 4 then 3 else c

theorem rawReverse_involutive (c : Fin 5) :
    rawReverse (rawReverse c) = c := by
  fin_cases c <;> decide

/-- The raw palette maps 0,1,2 to the corresponding effective
colours, and BOTH 3 and 4 to effective colour 3. -/
def rawPhi (c : Fin 5) : G4 :=
  Multiplicative.ofAdd
    (if c.val = 4 then (3 : ZMod 4) else (c.val : ZMod 4))

theorem rawPhi_surjective : Function.Surjective rawPhi := by
  decide

theorem rawPhi_equivariant (c : Fin 5) :
    rawPhi (rawReverse c) = identityReversal (rawPhi c) := by
  fin_cases c <;> decide

/-- Fully explicit finite group/reversal/raw-fibre datum. -/
def c4Datum : RawDatum G4 (Fin 5) where
  s := identityReversal
  reverse := rawReverse
  reverse_involutive := rawReverse_involutive
  phi := rawPhi
  phi_surjective := rawPhi_surjective
  equivariant := rawPhi_equivariant

/-- The orbit of the identity (additive 0) is the good
two-element orbit {0,2}. -/
theorem hasCompleteGoodOrbit : c4Datum.HasCompleteGoodOrbit := by
  change ∃ (g : G4),
    (∃ c : Fin 5, c4Datum.phi c = g ∧ c4Datum.reverse c = c) ∧
    ∀ a : G4, ∃ c : Fin 5,
      c4Datum.phi c = congruence c4Datum.s a g ∧
      c4Datum.reverse c = c
  refine ⟨1, ⟨0, by decide, by decide⟩, ?_⟩
  intro a
  fin_cases a
  all_goals first
    | exact ⟨0, by decide, by decide⟩
    | exact ⟨2, by decide, by decide⟩

/-- The other congruence orbit {1,3} has one good and one bad
effective colour, so global saturation fails. -/
theorem notCongruenceSaturated :
    ¬ c4Datum.IsCongruenceSaturated := by
  intro h
  let a : G4 := Multiplicative.ofAdd (1 : ZMod 4)
  have hg : a ∈ c4Datum.selfReverseEffective :=
    ⟨(1 : Fin 5), by decide, by decide⟩
  have hBad := h a a hg
  have hCongruence :
      congruence c4Datum.s a a =
        (Multiplicative.ofAdd (3 : ZMod 4) : G4) := by
    decide
  rw [hCongruence] at hBad
  obtain ⟨c, hc, hf⟩ := hBad
  have hNoFixedThree (r : Fin 5) :
      c4Datum.phi r =
        (Multiplicative.ofAdd (3 : ZMod 4) : G4) →
      c4Datum.reverse r ≠ r := by
    fin_cases r <;> decide
  exact (hNoFixedThree c hc) hf

/-- The effective group really has four elements and is not
the exceptional G=1 case. -/
theorem nontrivialEffectiveGroup : ¬ Subsingleton G4 := by
  intro h
  letI : Subsingleton G4 := h
  have heq : (0 : ZMod 4) = 1 := by
    have hGroup :
        (Multiplicative.ofAdd (0 : ZMod 4) : G4) =
          Multiplicative.ofAdd (1 : ZMod 4) :=
      Subsingleton.elim _ _
    exact congrArg Multiplicative.toAdd hGroup
  have hNe : (0 : ZMod 4) ≠ 1 := by decide
  exact hNe heq

/-- The actual original binary E/R_c Fraisse class admits a
countable homogeneous full-age model with a dense locally finite
subgroup of its full original-relational automorphism group. -/
theorem relationalDLF :
    c4Datum.HasCountableRelationalHomogeneousDLF := by
  exact (c4Datum.countableRelationalHomogeneousDLF_iff).2
    (Or.inr hasCompleteGoodOrbit)

/-- Coherent EPPA fails in the SAME literal original-relational
class, despite ordinary EPPA and DLF both holding. -/
theorem notRelationalCoherentEPPA :
    ¬ c4Datum.HasFiniteRelationalCoherentEPPAInCanonicalUniverses := by
  intro hCoherent
  rcases (c4Datum.hasFiniteRelationalCoherentEPPAInCanonicalUniverses_iff).mp
    hCoherent with hTrivial | hConditions
  · exact nontrivialEffectiveGroup hTrivial
  · exact notCongruenceSaturated hConditions.2

end FourColourSeparation
end SemigenericEPPA
