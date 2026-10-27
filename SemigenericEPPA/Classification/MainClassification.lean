import SemigenericEPPA.Classification.SAPRowAmalgamation

/-!
# Converse classification of finite strong-amalgamation rectangle laws

The ORIGINAL binary E/R_c finite age of a general 2+2 predicate P has
strong amalgamation if and only if P is a noncommutative group-difference
rectangle law with a finite effective group and an affine involutive
reversal of colours.

Necessity uses literal strong amalgamation twice, to obtain row
amalgamation and corner completion on raw 2+2 matrices; the remaining
reconstruction is independent algebra. Sufficiency uses the existing
full finite *original-relational* strong amalgamation theorem, not a
weakened matrix-level substitute.

Only an unrestricted triangle base is covered. Ordinary AP without
strongness is NOT a hypothesis of this classification.
-/

namespace SemigenericEPPA.Classification

universe u

namespace RectangleRule

variable {C : Type} (R : RectangleRule C)

/-- The exact group-based description of P. The group is allowed to
be noncommutative and its reversal need not fix the identity.
The alphabet C is kept unchanged, with a surjective equivariant raw
palette projection. -/
def HasGroupRectangleDescription : Prop :=
  ∃ (G : Type) (instG : Group G) (finG : Finite G),
    letI : Group G := instG
    ∃ (d : RawDatum G C),
      d.reverse = R.reverse ∧
      ∀ a b c e,
        R.allowed a b c e ↔
          (d.phi a)⁻¹ * d.phi b =
            (d.phi c)⁻¹ * d.phi e

/-- The converse classification from Appendix A, with an exact
literal-language SAP predicate for ALL finite induced embeddings.
Finiteness of the reconstructed group is derived, not postulated. -/
theorem finiteStrongSAP_iff_groupRectangle
    [Finite C] [Nonempty C] :
    R.HasFiniteRuleStrongSAP ↔ R.HasGroupRectangleDescription := by
  classical
  constructor
  · intro hSAP
    have hrow := R.rowAmalgamation_of_finiteRuleStrongSAP hSAP
    have hcorner := R.cornerCompletion_of_finiteRuleStrongSAP hSAP
    let origin : C := Classical.choice ‹Nonempty C›
    refine ⟨R.ReconstructedGroup hrow hcorner, inferInstance,
      R.reconstructedGroup_finite hrow hcorner origin, ?_⟩
    refine ⟨R.reconstructedRawDatum hrow hcorner origin, rfl, ?_⟩
    intro a b c e
    exact R.allowed_iff_reconstructedRawDatum
      hrow hcorner origin a b c e
  · rintro ⟨G, instG, finG, d, hReverse, hAllowed⟩
    letI : Group G := instG
    have hrow : R.HasRowAmalgamation := by
      intro a b c e f g h₁ h₂
      apply (hAllowed c e f g).mpr
      exact ((hAllowed a b c e).mp h₁).symm.trans
        ((hAllowed a b f g).mp h₂)
    have hcorner : R.HasCornerCompletion := by
      intro a b c
      obtain ⟨d₀, hd₀⟩ :=
        d.phi_surjective (d.phi c * (d.phi a)⁻¹ * d.phi b)
      refine ⟨d₀, (hAllowed a b c d₀).mpr ?_⟩
      rw [hd₀]
      group
    exact @finiteRuleStrongSAP_of_reconstructedGroup C R hrow hcorner inferInstance

end RectangleRule
end SemigenericEPPA.Classification
