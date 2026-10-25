import SemigenericEPPA.Structure.DLFRelationalClassification
import SemigenericEPPA.Structure.DLFNormalizeFiniteRawToFin

/-!
# Canonical full age equals full arbitrary finite ORIGINAL relational age

The relational DLF criterion quantifies canonical finite raw
presentations on Fin n. Because every original E,R_c finite
rectangle has an exact functional raw representation, and because
every finite raw presentation has an exact canonical Fin copy,
this is equivalent to induced universality for ALL finite
original AllThoseEPPA.Structure (rectangleLanguage C) objects
on ARBITRARY finite carrier types.

The theorem below proves this equivalence explicitly for the
SAME original relational target A, without replacing it by
another homogeneous model or using a Fraisse existence theorem.
It preserves/refects original E and EVERY ordered R_c predicate.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

namespace IsRectangleStructure

variable {X : Type w}
variable {A : Structure (rectangleLanguage C) X}

/-- If A contains induced copies of all canonical finite raw
R1–R3 rectangles with literal E and R_c colours, then it
contains induced copies of EVERY original finite relational
R1–R3 structure on every finite vertex carrier. -/
theorem allFiniteRelationalAge_of_canonicalRaw
    (hA : IsRectangleStructure d A)
    (hFin : ∀ (n : ℕ) (P : RawRectanglePresentation d (Fin n)),
      ∃ e : Fin n → X,
        Function.Injective e ∧
        (∀ x y : Fin n,
          partRel A (e x) (e y) ↔ P.part x y) ∧
        (∀ (c : C) (x y : Fin n),
          rawRel A c (e x) (e y) ↔ P.colour x y = some c)) :
    ∀ (W : Type t) [Fintype W]
      (B : Structure (rectangleLanguage C) W),
      IsRectangleStructure d B →
      ∃ e : W → X,
        Function.Injective e ∧
        (∀ x y : W,
          partRel A (e x) (e y) ↔ partRel B x y) ∧
        (∀ (c : C) (x y : W),
          rawRel A c (e x) (e y) ↔ rawRel B c x y) := by
  classical
  have hRawFin : ∀ (n : ℕ) (P : RawRectanglePresentation d (Fin n)),
      ∃ e : Fin n → X,
        Function.Injective e ∧
        (∀ x y : Fin n,
          hA.toRawPresentation.part (e x) (e y) ↔ P.part x y) ∧
        (∀ x y : Fin n,
          hA.toRawPresentation.colour (e x) (e y) = P.colour x y) := by
    intro n P
    obtain ⟨e, he, hPart, hColour⟩ := hFin n P
    refine ⟨e, he, hPart, ?_⟩
    intro x y
    cases hc : P.colour x y with
    | none =>
        have hp : P.part x y := (P.colour_none_iff x y).mp hc
        have hPartA : partRel A (e x) (e y) :=
          (hPart x y).mpr hp
        exact (hA.rawOption_none_iff (e x) (e y)).mpr hPartA
    | some c =>
        have hRel : rawRel A c (e x) (e y) :=
          (hColour c x y).mpr hc
        exact (hA.rawOption_some_iff c (e x) (e y)).mpr hRel
  intro W _ B hB
  obtain ⟨e, he, hPart, hColour⟩ :=
    hA.toRawPresentation.inducedFiniteAge_of_canonicalFinAge
      hRawFin W hB.toRawPresentation
  refine ⟨e, he, hPart, ?_⟩
  intro c x y
  calc
    rawRel A c (e x) (e y) ↔
        hA.toRawPresentation.colour (e x) (e y) = some c :=
      (hA.rawOption_some_iff c (e x) (e y)).symm
    _ ↔ hB.toRawPresentation.colour x y = some c := by
      rw [hColour x y]
    _ ↔ rawRel B c x y :=
      hB.rawOption_some_iff c x y

end IsRectangleStructure

namespace RawDatum

/-- In the named relational DLF statement, full canonical raw
age really does imply full induced original relational age
of the SAME actual countable homogeneous relational witness. -/
theorem exists_fullArbitraryFiniteRelationalAge_of_DLF
    (d : RawDatum G C)
    (hDLF : d.HasCountableRelationalHomogeneousDLF) :
    ∃ (X : Type (max u v))
      (A : Structure (rectangleLanguage C) X)
      (hA : IsRectangleStructure d A),
      Countable X ∧
      (∀ (W : Type t) [Fintype W]
        (B : Structure (rectangleLanguage C) W),
        IsRectangleStructure d B →
        ∃ e : W → X,
          Function.Injective e ∧
          (∀ x y : W,
            partRel A (e x) (e y) ↔ partRel B x y) ∧
          (∀ (c : C) (x y : W),
            rawRel A c (e x) (e y) ↔ rawRel B c x y)) := by
  obtain ⟨X, A, hA, hCount, hAge, _hHom, _hDense⟩ := hDLF
  exact ⟨X, A, hA, hCount,
    hA.allFiniteRelationalAge_of_canonicalRaw hAge⟩

end RawDatum
end SemigenericEPPA
