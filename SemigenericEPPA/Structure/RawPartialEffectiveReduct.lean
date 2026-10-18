import SemigenericEPPA.Structure.EffectiveGeometry

/-!
# Genuine raw partial isomorphisms preserve the effective reduct

The raw EPPA proof first applies effective EPPA to the original
R1–R3 rectangle structure with every colour c replaced by phi(c).
It must be justified that an actual partial map preserving all raw
binary predicates P_c also preserves the derived effective F.

Here this is proved directly using the literal raw presentation
API, chosenRaw uniqueness on each cross-part pair, and the
effective-reduct colour compatibility already established.
No new colour-preservation hypothesis is imposed by the proof.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) V}

/-- A raw partial map preserves effective group-valued F on
every genuine cross-E pair as soon as it preserves each raw P_c.
This is a literal equality, not equality up to any gauge. -/
theorem IsRectangleStructure.partialRaw_preserves_effective
    (h : IsRectangleStructure d A)
    (S : Set V) (p : S → V)
    (hRaw : ∀ (x y : S) (c : C),
      rawRel A c x.val y.val ↔ rawRel A c (p x) (p y))
    (x y : S)
    (hxy : ¬h.toEffectiveGeometry.part x.val y.val) :
    h.toEffectiveGeometry.F (p x) (p y) =
      h.toEffectiveGeometry.F x.val y.val := by
  have hcross : ¬partRel A x.val y.val := hxy
  obtain ⟨c, hc, _⟩ := h.cross_unique x.val y.val hcross
  have hcTarget : rawRel A c (p x) (p y) :=
    (hRaw x y c).mp hc
  have hOldOption : h.rawOption x.val y.val = some c :=
    (h.rawOption_some_iff c x.val y.val).mpr hc
  have hNewOption : h.rawOption (p x) (p y) = some c :=
    (h.rawOption_some_iff c (p x) (p y)).mpr hcTarget
  have hOld := h.rawOption_phi_effectiveTotal
    x.val y.val c hOldOption
  have hNew := h.rawOption_phi_effectiveTotal
    (p x) (p y) c hNewOption
  exact hNew.symm.trans hOld

/-- Complete effective partial-isomorphism data follow from
preservation/reflection of E and all individual raw predicates.
This is the precise premise of finite_effectiveEPPA_witness
and is independent of the sizes of raw colour fibres. -/
theorem IsRectangleStructure.partialRaw_toEffective
    (h : IsRectangleStructure d A)
    (S : Set V) (p : S → V)
    (hE : ∀ x y : S,
      partRel A x.val y.val ↔ partRel A (p x) (p y))
    (hRaw : ∀ (x y : S) (c : C),
      rawRel A c x.val y.val ↔ rawRel A c (p x) (p y)) :
    (∀ x y : S,
      h.toEffectiveGeometry.part x.val y.val ↔
        h.toEffectiveGeometry.part (p x) (p y)) ∧
    (∀ x y : S, ¬h.toEffectiveGeometry.part x.val y.val →
      h.toEffectiveGeometry.F (p x) (p y) =
        h.toEffectiveGeometry.F x.val y.val) := by
  constructor
  · intro x y
    exact hE x y
  · intro x y hxy
    exact h.partialRaw_preserves_effective S p hRaw x y hxy

end SemigenericEPPA
