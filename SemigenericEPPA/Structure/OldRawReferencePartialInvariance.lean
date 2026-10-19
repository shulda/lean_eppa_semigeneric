import SemigenericEPPA.Structure.OldRawReferenceOnBase

/-!
# The fixed extended old raw reference respects all old partial maps

The total raw colour reference on a fixed effective base was chosen
BEFORE any partial map by reading the original functional raw
presentation through an injective embedding e.  Hence a partial
automorphism of the original raw structure automatically preserves
this reference on its old-old cross E pairs.

This is exactly the last raw-colour hypothesis of the zero-section
individual raw lift. No new reference map is chosen depending on
the partial map.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {U : Type w} {V : Type t}
variable {d : RawDatum G C}

/-- A genuine partial raw-colour isomorphism of the old presentation
preserves the fixed extended old reference on every cross pair of
its domain, under the prescribed effective embedding. -/
theorem oldRawReferenceOnBase_partialInvariant
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (e : U → V) (he : Function.Injective e)
    (c₀ : C)
    (hPart : ∀ x y : U, D.part (e x) (e y) ↔ P.part x y)
    (S : Set U) (p : S → U)
    (hE : ∀ x y : S, P.part x.val y.val ↔
      P.part (p x) (p y))
    (hRaw : ∀ x y : S,
      P.colour (p x) (p y) = P.colour x.val y.val)
    (x y : S)
    (hcross : ¬D.part (e x.val) (e y.val)) :
    oldRawReferenceOnBase P e c₀ (e (p x)) (e (p y)) =
      oldRawReferenceOnBase P e c₀ (e x.val) (e y.val) := by
  have hab : ¬P.part x.val y.val := by
    intro hp
    exact hcross ((hPart x.val y.val).mpr hp)
  have hpab : ¬P.part (p x) (p y) := by
    intro hp
    exact hab ((hE x y).mpr hp)
  have hOld := P.totalOldRawColour_cross x.val y.val hab
  have hNew := P.totalOldRawColour_cross (p x) (p y) hpab
  have hColour :
      P.totalOldRawColour (p x) (p y) =
        P.totalOldRawColour x.val y.val := by
    apply Option.some.inj
    calc
      some (P.totalOldRawColour (p x) (p y)) =
          P.colour (p x) (p y) := hNew.symm
      _ = P.colour x.val y.val := hRaw x y
      _ = some (P.totalOldRawColour x.val y.val) := hOld
  rw [oldRawReferenceOnBase_old P e he c₀,
      oldRawReferenceOnBase_old P e he c₀]
  exact hColour

end SemigenericEPPA
