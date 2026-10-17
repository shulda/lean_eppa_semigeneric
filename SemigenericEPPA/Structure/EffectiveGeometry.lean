import SemigenericEPPA.Structure.EffectiveColour
import SemigenericEPPA.Structure.RelationalRoundtrip
import SemigenericEPPA.Structure.EffectiveRawExtension

/-!
# Effective E-rectangle geometries and canonical old-structure colours

We separate the effective group-valued geometry from the raw fibres:
  • an equivalence relation E;
  • a total function F, whose values on E-related pairs are immaterial;
  • reversal s on cross-part pairs;
  • the exact noncommutative rectangle equation.

Every literal R1--R3 structure produces such geometry. On pairs within
the same E-class, the extracted function uses 1 ∈ G solely as an
irrelevant dummy. Its reversal is asserted ONLY for cross-part pairs,
since an arbitrary affine anti-involution need not satisfy s(1)=1.

This is the input type for the effective phase of one-point SAP and
makes the existing raw completion theorem directly applicable.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v} {V : Type w}

/-- The effective component of a generalized semigeneric rectangle
structure. The dummy F-values on pairs in the same class impose
no requirements whatsoever. -/
structure EffectiveGeometry (s : AffineAntiInvolution G) (V : Type w) where
  part : Setoid V
  F : V → V → G
  reverse_cross : ∀ x y, ¬part x y → F y x = s (F x y)
  rectangle :
    ∀ x₀ x₁ y₀ y₁,
      part x₀ x₁ → part y₀ y₁ → ¬part x₀ y₀ →
      (F x₀ y₀)⁻¹ * F x₀ y₁ =
        (F x₁ y₀)⁻¹ * F x₁ y₁

namespace EffectiveGeometry

variable {s : AffineAntiInvolution G}

/-- The two other entries of a rectangle, and the fourth one, are
cross-part whenever its first entry is. -/
theorem cross_square (D : EffectiveGeometry s V)
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

/-- Same-part values may be changed freely, provided the cross-part
values remain unchanged. This includes empty and one-part structures. -/
theorem of_cross_eq
    (D : EffectiveGeometry s V) (F' : V → V → G)
    (hcross : ∀ x y, ¬D.part x y → F' x y = D.F x y) :
    ∃ D' : EffectiveGeometry s V,
      D'.part = D.part ∧
      D'.F = F' := by
  let D' : EffectiveGeometry s V := {
    part := D.part
    F := F'
    reverse_cross := by
      intro x y hxy
      have hyx : ¬D.part y x := by
        intro hyx
        exact hxy (D.part.iseqv.symm hyx)
      rw [hcross y x hyx, hcross x y hxy]
      exact D.reverse_cross x y hxy
    rectangle := by
      intro x₀ x₁ y₀ y₁ hx hy h00
      obtain ⟨h01, h10, h11⟩ := D.cross_square x₀ x₁ y₀ y₁ hx hy h00
      rw [hcross x₀ y₀ h00, hcross x₀ y₁ h01,
        hcross x₁ y₀ h10, hcross x₁ y₁ h11]
      exact D.rectangle x₀ x₁ y₀ y₁ hx hy h00
  exact ⟨D', rfl, rfl⟩

end EffectiveGeometry

namespace IsRectangleStructure

variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) V}

/-- The exact effective colour from a relational R1--R3 structure,
extended by a harmless dummy 1 on pairs inside E-classes. -/
noncomputable def effectiveTotal (h : IsRectangleStructure d A)
    (x y : V) : G := by
  classical
  exact if hxy : partRel A x y then 1 else h.chosenEffective x y hxy

@[simp] theorem effectiveTotal_same (h : IsRectangleStructure d A)
    (x y : V) (hxy : partRel A x y) :
    h.effectiveTotal x y = 1 := by
  simp [effectiveTotal, hxy]

theorem effectiveTotal_cross (h : IsRectangleStructure d A)
    (x y : V) (hxy : ¬partRel A x y) :
    h.effectiveTotal x y = h.chosenEffective x y hxy := by
  simp [effectiveTotal, hxy]

/-- Raw E-classes and effective colours from any actual R1--R3
structure form an effective E-rectangle geometry. -/
noncomputable def toEffectiveGeometry
    (h : IsRectangleStructure d A) : EffectiveGeometry d.s V where
  part := h.partSetoid
  F := h.effectiveTotal
  reverse_cross := by
    intro x y hxy
    have hyx := h.cross_symm hxy
    rw [h.effectiveTotal_cross y x hyx,
      h.effectiveTotal_cross x y hxy]
    exact h.chosenEffective_reverse x y hxy hyx
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy h00
    obtain ⟨h01, h10, h11⟩ :=
      h.cross_square x₀ x₁ y₀ y₁ hx hy h00
    rw [h.effectiveTotal_cross x₀ y₀ h00,
      h.effectiveTotal_cross x₀ y₁ h01,
      h.effectiveTotal_cross x₁ y₀ h10,
      h.effectiveTotal_cross x₁ y₁ h11]
    exact h.chosenEffective_rectangle x₀ x₁ y₀ y₁
      hx hy h00 h01 h10 h11

@[simp] theorem toEffectiveGeometry_part
    (h : IsRectangleStructure d A) (x y : V) :
    h.toEffectiveGeometry.part x y ↔ partRel A x y :=
  Iff.rfl

/-- The raw option function is compatible with the extracted total
effective colours on its entire prescribed domain. -/
theorem rawOption_phi_effectiveTotal
    (h : IsRectangleStructure d A) (x y : V) (c : C)
    (hc : h.rawOption x y = some c) :
    d.phi c = h.effectiveTotal x y := by
  have hraw := (h.rawOption_some_iff c x y).mp hc
  have hcross : ¬partRel A x y :=
    h.raw_only_cross c x y hraw
  rw [h.effectiveTotal_cross x y hcross]
  change d.phi c = d.phi (h.chosenRaw x y hcross)
  exact congrArg d.phi (h.chosenRaw_unique x y hcross c hraw).symm

/-- The actual old-structure raw colours and its effective geometry
are mutually compatible. This is the canonical input to the raw
completion interface, not an assumption of a new theorem. -/
theorem rawOption_compatible (h : IsRectangleStructure d A) :
    ∀ x y c, h.rawOption x y = some c →
      d.phi c = h.toEffectiveGeometry.F x y := by
  intro x y c hc
  exact h.rawOption_phi_effectiveTotal x y c hc

end IsRectangleStructure

end SemigenericEPPA
