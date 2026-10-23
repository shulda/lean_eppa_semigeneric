import SemigenericEPPA.Algebra.CongruenceAction

/-!
# DLF safe-colour predicates are invariant along a COMPLETE good orbit

Full coherent EPPA requires the set of all reversal-fixed raw-colour
fibres to be globally saturated under the affine congruence action.
The relative DLF construction needs a weaker local condition:
a PARTICULAR effective colour g has its entire congruence orbit
inside the genuinely self-reversing raw fibres.

This module treats that colour-specific condition directly and proves
it is invariant under every affine congruence translation. In
particular no global saturation, s(1)=1, commutativity, or selected
recentring is needed. This supplies the exact algebraic closure
needed when the relative finite H-action conjugates previously safe
cross-E pairs or changes the valuation gauge.

These are local algebra lemmas, not a construction of a safe group
or a dense locally finite subgroup.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

namespace RawDatum

/-- A particular effective colour lies in a COMPLETE good
congruence orbit, unlike the stronger global saturation of all
good effective colours. -/
def GoodCompleteOrbitAt (d : RawDatum G C) (g : G) : Prop :=
  ∀ a : G, congruence d.s a g ∈ d.selfReverseEffective

/-- A locally safe colour is automatically genuinely good:
evaluate its complete-orbit condition at the identity. -/
theorem good_of_completeOrbitAt
    (d : RawDatum G C) (g : G)
    (hg : d.GoodCompleteOrbitAt g) :
    g ∈ d.selfReverseEffective := by
  simpa only [GoodCompleteOrbitAt, congruence_one] using hg 1

/-- An affine translate of a locally complete good orbit remains in
the SAME complete good orbit, for arbitrary nonabelian G. -/
theorem goodCompleteOrbitAt_congruence
    (d : RawDatum G C)
    (g b : G)
    (hg : d.GoodCompleteOrbitAt g) :
    d.GoodCompleteOrbitAt (congruence d.s b g) := by
  intro a
  rw [← congruence_mul]
  exact hg (a * b)

/-- The local DLF safe-orbit predicate is unchanged by any affine
congruence move; use the inverse group element for the converse. -/
theorem goodCompleteOrbitAt_congruence_iff
    (d : RawDatum G C)
    (g b : G) :
    d.GoodCompleteOrbitAt (congruence d.s b g) ↔
      d.GoodCompleteOrbitAt g := by
  constructor
  · intro hg a
    have h := hg (a * b⁻¹)
    change congruence d.s (a * b⁻¹)
      (congruence d.s b g) ∈ d.selfReverseEffective at h
    rw [← congruence_mul] at h
    have hab : (a * b⁻¹) * b = a := by group
    rw [hab] at h
    exact h
  · exact d.goodCompleteOrbitAt_congruence g b

/-- Witnessing one complete good congruence orbit supplies the
local safe predicate at an ACTUAL good seed, not just a fixed
effective colour with no raw reversal witness. -/
theorem hasCompleteGoodOrbit_iff_exists_goodCompleteOrbitAt
    (d : RawDatum G C) :
    d.HasCompleteGoodOrbit ↔
      ∃ g : G, d.GoodCompleteOrbitAt g := by
  constructor
  · rintro ⟨g, _hg, horbit⟩
    exact ⟨g, horbit⟩
  · rintro ⟨g, horbit⟩
    exact ⟨g, d.good_of_completeOrbitAt g horbit, horbit⟩

end RawDatum

end SemigenericEPPA
