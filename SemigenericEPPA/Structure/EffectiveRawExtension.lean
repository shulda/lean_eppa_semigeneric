import SemigenericEPPA.Algebra.PrescribedRawLift
import SemigenericEPPA.Structure.RawPresentation

/-!
# From effective rectangles to genuine raw rectangle structures

This is the precise interface between the effective group-valued
amalgamation problem and the full raw-coloured language L_C.

Given an E-equivalence relation, effective colours F with the
reversal/rectangle laws, and reversal-compatible prescribed raw
colours mapping to F, we construct a full member of K(G,s,φ).
All prescribed raw colours remain literally unchanged.

The temporary linear order is used ONLY to orient previously
uncoloured unordered cross-part edges; in finite applications a
linear order is chosen on the finite carrier. No global S condition,
self-reversing raw colours or EPPA theorem is assumed.

The remaining SAP task is to construct the appropriate effective
geometry F from a genuine one-point amalgamation diagram.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} [LinearOrder V]

/-- Effective E-rectangle geometry with a compatible prescribed partial
raw colouring. This deliberately packages ALL the hypotheses needed for
a raw lift; none of them is hidden behind a choice or a new axiom. -/
structure EffectiveRawExtension (d : RawDatum G C) (V : Type w) where
  part : Setoid V
  effective : V → V → G
  prescribed : V → V → Option C
  prescribed_same : ∀ x y, part x y → prescribed x y = none
  prescribed_reverse : ∀ x y,
    prescribed y x = Option.map d.reverse (prescribed x y)
  prescribed_effective : ∀ x y c,
    prescribed x y = some c → d.phi c = effective x y
  effective_reverse : ∀ x y, ¬part x y →
    effective y x = d.s (effective x y)
  effective_rectangle :
    ∀ x₀ x₁ y₀ y₁,
      part x₀ x₁ → part y₀ y₁ → ¬part x₀ y₀ →
      (effective x₀ y₀)⁻¹ * effective x₀ y₁ =
        (effective x₁ y₀)⁻¹ * effective x₁ y₁

namespace EffectiveRawExtension

variable {d : RawDatum G C}
variable (D : EffectiveRawExtension d V)

/-- A cross-part pair in one corner of a rectangle makes all four
corners cross-part, using only equivalence of E. -/
private theorem cross_square
    (x₀ x₁ y₀ y₁ : V)
    (hx : D.part x₀ x₁) (hy : D.part y₀ y₁)
    (h00 : ¬D.part x₀ y₀) :
    (¬D.part x₀ y₁) ∧
    (¬D.part x₁ y₀) ∧
    (¬D.part x₁ y₁) := by
  constructor
  · intro h01
    exact h00 (D.part.iseqv.trans h01 (D.part.iseqv.symm hy))
  constructor
  · intro h10
    exact h00 (D.part.iseqv.trans hx h10)
  · intro h11
    exact h00
      (D.part.iseqv.trans hx
        (D.part.iseqv.trans h11 (D.part.iseqv.symm hy)))

/-- A complete functional raw colouring, satisfying every R1--R3
axiom, constructed using only the effective data and φ-surjectivity. -/
noncomputable def toPresentation : RawRectanglePresentation d V where
  part := D.part
  part_equiv := D.part.iseqv
  colour := d.completeRaw D.part D.prescribed D.effective
  colour_none_iff := by
    intro x y
    constructor
    · intro hnone
      by_contra hcross
      obtain ⟨c, hc⟩ :=
        d.completeRaw_cross D.part D.prescribed D.effective x y hcross
      rw [hnone] at hc
      cases hc
    · intro hpart
      exact d.completeRaw_same D.part D.prescribed D.effective x y hpart
  colour_reverse := by
    intro x y
    exact d.completeRaw_reverse D.part D.part.iseqv
      D.prescribed D.effective x y
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁ h00 h01 h10 h11
    have hcross00 : ¬D.part x₀ y₀ := by
      intro hpart
      have hnone :=
        d.completeRaw_same D.part D.prescribed D.effective
          x₀ y₀ hpart
      rw [h00] at hnone
      cases hnone
    obtain ⟨hcross01, hcross10, hcross11⟩ :=
      D.cross_square x₀ x₁ y₀ y₁ hx hy hcross00
    have he00 := d.completeRaw_phi D.part D.part.iseqv
      D.prescribed D.effective D.prescribed_effective
      D.effective_reverse x₀ y₀ hcross00 c₀₀ h00
    have he01 := d.completeRaw_phi D.part D.part.iseqv
      D.prescribed D.effective D.prescribed_effective
      D.effective_reverse x₀ y₁ hcross01 c₀₁ h01
    have he10 := d.completeRaw_phi D.part D.part.iseqv
      D.prescribed D.effective D.prescribed_effective
      D.effective_reverse x₁ y₀ hcross10 c₁₀ h10
    have he11 := d.completeRaw_phi D.part D.part.iseqv
      D.prescribed D.effective D.prescribed_effective
      D.effective_reverse x₁ y₁ hcross11 c₁₁ h11
    rw [he00, he01, he10, he11]
    exact D.effective_rectangle x₀ x₁ y₀ y₁ hx hy hcross00

/-- The output lives in the literal AllThoseEPPA relational API. -/
noncomputable def toStructure :
    Structure (rectangleLanguage C) V :=
  D.toPresentation.toStructure

/-- Every effective extension datum produces a genuine object of K(G,s,φ),
rather than merely a compatible group-valued matrix. -/
theorem toStructure_isRectangleStructure :
    IsRectangleStructure d D.toStructure :=
  D.toPresentation.toStructure_isRectangleStructure

/-- The actual E-relation in the resulting relational structure is
exactly the specified equivalence relation, not a quotient or refinement. -/
theorem toStructure_part (x y : V) :
    partRel D.toStructure x y ↔ D.part x y := by
  change D.toPresentation.part x y ↔ D.part x y
  rfl

/-- Crucial for induced embeddings: every prescribed old raw edge has
exactly its prescribed label in the final relational structure. -/
theorem toStructure_prescribed
    (x y : V) (c : C) (hc : D.prescribed x y = some c) :
    rawRel D.toStructure c x y := by
  change d.completeRaw D.part D.prescribed D.effective x y = some c
  exact d.completeRaw_prescribed D.part D.part.iseqv
    D.prescribed D.effective D.prescribed_same D.prescribed_reverse
    x y c hc

end EffectiveRawExtension
end SemigenericEPPA
