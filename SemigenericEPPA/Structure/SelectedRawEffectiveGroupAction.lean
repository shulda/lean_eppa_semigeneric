import SemigenericEPPA.Structure.SelectedRawInducedGroupData

/-!
# Genuine raw automorphism actions preserve the induced effective geometry

For the fixed common-witness nontrivial-G construction, the only
permitted starting data for a stabilizer H is its actual action
by E- and EVERY raw-colour-preserving automorphisms on a selected
old substructure S. The effective factorial-projection theorem
expects E/F preservation on the literal induced effective geometry.

These are not independent hypotheses. We derive exact effective
E and F invariance from the genuine old raw action by applying
the verified relational-to-effective bridge on cross-class pairs.

No ambient old action on vertices outside S is postulated.
No commutativity, affine recentering, raw self-reversing colour or
orbit saturation assumption is used.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {C : Type v} {A : Type w}
variable {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- An actual raw automorphism action of an induced S preserves
literally the canonical E/F reduct on that SAME S.
These are the two inputs to the factorial occupied-projection
construction, derived solely from genuine raw data. -/
theorem selectedRawAction_preserves_effective
    (P : RawRectanglePresentation d A)
    (S : Set A)
    (rho : H →* Equiv.Perm S)
    (hPart : ∀ (h : H) (x y : S),
      P.part (rho h x).val (rho h y).val ↔ P.part x.val y.val)
    (hColour : ∀ (h : H) (x y : S),
      P.colour (rho h x).val (rho h y).val =
        P.colour x.val y.val) :
    (∀ (h : H) (x y : S),
      P.effectiveReduct.part x.val y.val ↔
        P.effectiveReduct.part (rho h x).val (rho h y).val) ∧
    (∀ (h : H) (x y : S),
      ¬P.effectiveReduct.part x.val y.val →
        P.effectiveReduct.F (rho h x).val (rho h y).val =
          P.effectiveReduct.F x.val y.val) := by
  constructor
  · intro h x y
    exact (P.effectiveReduct_part x.val y.val).trans
      ((hPart h x y).symm.trans
        (P.effectiveReduct_part (rho h x).val
          (rho h y).val).symm)
  · intro h x y hcross
    have hxy : ¬P.part x.val y.val := by
      intro hp
      exact hcross ((P.effectiveReduct_part x.val y.val).mpr hp)
    have hnew : ¬P.part (rho h x).val (rho h y).val := by
      intro hp
      exact hxy ((hPart h x y).mp hp)
    exact P.effectiveReduct_equalColour
      (rho h x).val (rho h y).val x.val y.val
      (hColour h x y) hnew

end RawRectanglePresentation

end SemigenericEPPA
