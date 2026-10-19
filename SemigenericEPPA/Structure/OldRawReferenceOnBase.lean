import SemigenericEPPA.Structure.TotalOldRawPalette
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge

/-!
# Extend old raw cross-colours along a fixed effective embedding

The raw-cover fixed-baseline lemma takes a TOTAL raw reference
old : V → V → C on the effective base, but only assumes equations on
the embedded old subset S₀. The original raw presentation P already
provides the exact raw colours on that subset; no arbitrary
H-dependent choice of references should be needed.

Use a partial inverse to an injective old effective embedding
e : U → V and one harmless default c₀∈C to extend P's actual
raw-colour function over all of V. At old image points the reference
agrees EXACTLY with P.totalOldRawColour, and satisfies the required
raw/effective projection and reversal equations on every old-old
cross-E pair. Outside the old range no equations are claimed.

This fixes the raw reference before any later induced substructure,
group H, or partial isomorphism.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {U : Type w} {V : Type t}
variable {d : RawDatum G C}

/-- Totalize the raw colour of a genuine old structure along an
injective old map; values outside the old image are irrelevant. -/
noncomputable def oldRawReferenceOnBase
    (P : RawRectanglePresentation d U)
    (e : U → V)
    (c₀ : C)
    (x y : V) : C := by
  classical
  exact if hx : x ∈ Set.range e then
    if hy : y ∈ Set.range e then
      P.totalOldRawColour (Classical.choose hx) (Classical.choose hy)
    else c₀
  else c₀

/-- On the old image, the totalized reference is LITERALLY the
raw colour of the old structure, including irrelevant same-E pairs. -/
theorem oldRawReferenceOnBase_old
    (P : RawRectanglePresentation d U)
    (e : U → V) (he : Function.Injective e)
    (c₀ : C) (a b : U) :
    oldRawReferenceOnBase P e c₀ (e a) (e b) =
      P.totalOldRawColour a b := by
  classical
  unfold oldRawReferenceOnBase
  split_ifs with hx hy
  · have ha : Classical.choose hx = a := he (Classical.choose_spec hx)
    have hb : Classical.choose hy = b := he (Classical.choose_spec hy)
    rw [ha, hb]
  · exact False.elim (hy ⟨b, rfl⟩)
  · exact False.elim (hx ⟨a, rfl⟩)

/-- The extended reference has the correct effective colour on
all old cross-E pairs, even if the rest of V has no raw colouring. -/
theorem oldRawReferenceOnBase_phi
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (e : U → V) (he : Function.Injective e)
    (c₀ : C)
    (hpart : ∀ a b : U, D.part (e a) (e b) ↔ P.part a b)
    (hF : ∀ a b : U, ∀ c : C,
      P.colour a b = some c → d.phi c = D.F (e a) (e b))
    (x y : V) (hx : x ∈ Set.range e) (hy : y ∈ Set.range e)
    (hxy : ¬D.part x y) :
    d.phi (oldRawReferenceOnBase P e c₀ x y) = D.F x y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : ¬P.part a b := by
    intro h
    exact hxy ((hpart a b).mpr h)
  rw [oldRawReferenceOnBase_old P e he]
  exact hF a b _ (P.totalOldRawColour_cross a b hab)

/-- Exact raw reversal on old-old cross-E pairs, with no assumption
that the arbitrary default c₀ is self-reversing. -/
theorem oldRawReferenceOnBase_reverse
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (e : U → V) (he : Function.Injective e)
    (c₀ : C)
    (hpart : ∀ a b : U, D.part (e a) (e b) ↔ P.part a b)
    (x y : V) (hx : x ∈ Set.range e) (hy : y ∈ Set.range e)
    (hxy : ¬D.part x y) :
    oldRawReferenceOnBase P e c₀ y x =
      d.reverse (oldRawReferenceOnBase P e c₀ x y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : ¬P.part a b := by
    intro h
    exact hxy ((hpart a b).mpr h)
  rw [oldRawReferenceOnBase_old P e he,
      oldRawReferenceOnBase_old P e he]
  exact P.totalOldRawColour_reverse a b hab

end SemigenericEPPA
