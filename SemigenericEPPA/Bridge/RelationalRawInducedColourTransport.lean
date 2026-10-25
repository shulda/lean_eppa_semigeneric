import SemigenericEPPA.Bridge.NativeRelationalSemiCoherentEP
import SemigenericEPPA.Structure.RelationalRoundtrip

/-!
# Exact preservation/reflection of raw colours for literal relational maps

For two distinct original R1--R3 structures, preserving/reflection of
E and every ordered binary R_c is EQUIVALENT to exact equality of
their Option-C raw colours on each ordered vertex pair.

The two structures may have different carriers; f need not be
surjective. These explicit conversion lemmas are the finitary core
of the bridge between native relational semi-coherent EP and the
already certified unrestricted raw subgroup-action property.
No safety or group-commutativity hypothesis is involved.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {X : Type w} {Y : Type z}
variable {P : Structure (rectangleLanguage C) X}
variable {Q : Structure (rectangleLanguage C) Y}

/-- An original E/R_c induced map preserves every COMPLETE raw
Option-C colour, including the absence of a cross colour on E. -/
theorem IsRectangleStructure.rawOption_eq_of_induced
    (hP : IsRectangleStructure d P)
    (hQ : IsRectangleStructure d Q)
    (f : X → Y)
    (hPart : ∀ x y : X,
      partRel Q (f x) (f y) ↔ partRel P x y)
    (hRaw : ∀ (c : C) (x y : X),
      rawRel Q c (f x) (f y) ↔ rawRel P c x y)
    (x y : X) :
    hQ.toRawPresentation.colour (f x) (f y) =
      hP.toRawPresentation.colour x y := by
  change hQ.rawOption (f x) (f y) = hP.rawOption x y
  cases hc : hP.rawOption x y with
  | none =>
      have hp : partRel P x y :=
        (hP.rawOption_none_iff x y).mp hc
      have hq : hQ.rawOption (f x) (f y) = none :=
        (hQ.rawOption_none_iff (f x) (f y)).mpr
          ((hPart x y).mpr hp)
      exact hq
  | some c =>
      have hp : rawRel P c x y :=
        (hP.rawOption_some_iff c x y).mp hc
      have hq : hQ.rawOption (f x) (f y) = some c :=
        (hQ.rawOption_some_iff c (f x) (f y)).mpr
          ((hRaw c x y).mpr hp)
      exact hq

/-- Conversely, equality of raw Option-C colours preserves and
reflects each original ordered relation R_c literally. -/
theorem IsRectangleStructure.rawRel_iff_of_rawColour_eq
    (hP : IsRectangleStructure d P)
    (hQ : IsRectangleStructure d Q)
    (f : X → Y)
    (hColour : ∀ x y : X,
      hQ.toRawPresentation.colour (f x) (f y) =
        hP.toRawPresentation.colour x y)
    (c : C) (x y : X) :
    rawRel Q c (f x) (f y) ↔ rawRel P c x y := by
  calc
    rawRel Q c (f x) (f y) ↔
        hQ.rawOption (f x) (f y) = some c :=
      (hQ.rawOption_some_iff c (f x) (f y)).symm
    _ ↔ hP.rawOption x y = some c := by
      have hh : hQ.rawOption (f x) (f y) = hP.rawOption x y :=
        hColour x y
      rw [← hh]
    _ ↔ rawRel P c x y :=
      hP.rawOption_some_iff c x y

end SemigenericEPPA
