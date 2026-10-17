import SemigenericEPPA.Structure.Language

/-!
# A functional raw-colour presentation of rectangle structures

An E-equivalence relation plus an Option-valued raw colour function
is often much easier to construct than a general relational structure.
This module gives the literal correspondence from such data to the
AllThoseEPPA binary language used throughout the formalization.

The output is a *genuine* rectangle-language structure, and the
entire class predicate R1--R3 follows without extra assumptions.
In particular a raw-colour completion can be used as an ordinary
member of the exact manuscript class, rather than an abstract matrix.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v} {V : Type w}

/-- Functional encoding of all R1--R3 data. Same-class pairs have
no colour; every cross-class pair has exactly one, with reversal and
the effective group-valued rectangle equation. -/
structure RawRectanglePresentation (d : RawDatum G C) (V : Type w) where
  part : V → V → Prop
  part_equiv : Equivalence part
  colour : V → V → Option C
  colour_none_iff : ∀ x y, colour x y = none ↔ part x y
  colour_reverse : ∀ x y,
    colour y x = Option.map d.reverse (colour x y)
  rectangle :
    ∀ (x₀ x₁ y₀ y₁ : V),
      part x₀ x₁ → part y₀ y₁ →
      ∀ (c₀₀ c₀₁ c₁₀ c₁₁ : C),
        colour x₀ y₀ = some c₀₀ →
        colour x₀ y₁ = some c₀₁ →
        colour x₁ y₀ = some c₁₀ →
        colour x₁ y₁ = some c₁₁ →
        (d.phi c₀₀)⁻¹ * d.phi c₀₁ =
          (d.phi c₁₀)⁻¹ * d.phi c₁₁

namespace RawRectanglePresentation

variable {d : RawDatum G C}
variable (P : RawRectanglePresentation d V)

/-- Interpret the exact binary symbols E and P_c from the functional
data. Casting the tuple indices through n=2 avoids a competing language
representation or any non-binary relation. -/
def toStructure : Structure (rectangleLanguage C) V where
  rel := fun {n} R tuple =>
    match R.val with
    | none =>
        P.part
          (tuple (Fin.cast R.property.symm 0))
          (tuple (Fin.cast R.property.symm 1))
    | some c =>
        P.colour
          (tuple (Fin.cast R.property.symm 0))
          (tuple (Fin.cast R.property.symm 1)) = some c
  func := fun {n} F _ => PEmpty.elim F

@[simp] theorem partRel_toStructure (x y : V) :
    partRel P.toStructure x y ↔ P.part x y := by
  rfl

@[simp] theorem rawRel_toStructure (c : C) (x y : V) :
    rawRel P.toStructure c x y ↔ P.colour x y = some c := by
  rfl

/-- A functional presentation gives an actual member of K(G,s,phi)
with the literal R1--R3 axioms of the manuscript. -/
theorem toStructure_isRectangleStructure :
    IsRectangleStructure d P.toStructure := by
  refine {
    parts_equiv := ?_
    raw_only_cross := ?_
    cross_unique := ?_
    reverse := ?_
    rectangle := ?_ }
  · exact P.part_equiv
  · intro c x y hc hpart
    have hc' : P.colour x y = some c := hc
    have hn : P.colour x y = none :=
      (P.colour_none_iff x y).2 hpart
    rw [hc'] at hn
    cases hn
  · intro x y hxy
    have hc : P.colour x y ≠ none := by
      intro hnone
      exact hxy ((P.colour_none_iff x y).1 hnone)
    cases heq : P.colour x y with
    | none =>
      exact (hc heq).elim
    | some c =>
      refine ⟨c, heq, ?_⟩
      intro c' hcol
      exact Option.some.inj (hcol.symm.trans heq)
  · intro c x y
    constructor
    · intro hc
      change P.colour x y = some c at hc
      change P.colour y x = some (d.reverse c)
      rw [P.colour_reverse x y, hc]
      rfl
    · intro hc
      change P.colour y x = some (d.reverse c) at hc
      change P.colour x y = some c
      have hrev := P.colour_reverse y x
      rw [hc] at hrev
      simpa only [Option.map_some, d.reverse_involutive] using hrev
  · intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁
      h00 h01 h10 h11
    exact P.rectangle x₀ x₁ y₀ y₁ hx hy
      c₀₀ c₀₁ c₁₀ c₁₁ h00 h01 h10 h11

end RawRectanglePresentation
end SemigenericEPPA
