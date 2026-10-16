import AllThoseEPPA.Structure
import SemigenericEPPA.Algebra.RawDatum
import Mathlib.Data.Setoid.Basic

/-!
# The literal finite binary language and its rectangle class

This module uses the EXISTING general language/structure API of
AllThoseEPPA.  It does not define competing maps or partial
isomorphisms and does not invoke an EPPA existence theorem.

For a raw colour type C, the only relation symbols are E and P_c,
all of arity two. The class predicate states precisely:
  R1. E is an equivalence relation;
  R2. exactly one raw colour on each ordered cross-part pair,
      no colours within parts, and reversal symmetry;
  R3. the group-valued noncommutative rectangle law.

The vertex type need not be finite; finiteness belongs in the theorem
hypotheses. Equality of rows or columns causes only tautological
rectangle equations, so no distinctness assumptions are necessary.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

/-- Exactly one symbol E plus a family P_c, all binary; no functions. -/
def rectangleLanguage (C : Type u) : Language.{u} where
  RelSymbol := fun n => { symbol : Option C // n = 2 }
  FuncSymbol := fun _ => PEmpty.{u+1}
  relArity_pos := by
    intro n R
    have hn : n = 2 := R.property
    subst n
    decide

instance rectangleLanguage_isRelational (C : Type u) :
    (rectangleLanguage C).IsRelational where
  func_isEmpty := fun _ => ⟨PEmpty.elim⟩

/-- Literal binary relation symbols: none for E, some c for P_c. -/
def binarySymbol (C : Type u) (name : Option C) :
    (rectangleLanguage C).RelSymbol 2 :=
  ⟨name, rfl⟩

/-- The ordered tuple (x,y), never an unordered pair. -/
def pairTuple {V : Type v} (x y : V) : Fin 2 → V :=
  fun i => if i.val = 0 then x else y

variable {C : Type u} {V : Type v}

/-- The distinguished equivalence relation E. -/
def partRel (A : Structure (rectangleLanguage C) V) (x y : V) : Prop :=
  A.rel (binarySymbol C none) (pairTuple x y)

/-- The literal raw-colour predicate P_c. -/
def rawRel (A : Structure (rectangleLanguage C) V)
    (c : C) (x y : V) : Prop :=
  A.rel (binarySymbol C (some c)) (pairTuple x y)

/-- Every relation symbol in the language has arity exactly 2. -/
theorem rectangleSymbol_arity {n : ℕ}
    (R : (rectangleLanguage C).RelSymbol n) : n = 2 :=
  R.property

variable {G : Type w} [Group G]

/-- The literal axioms (R1)--(R3) of the finite class K(G,s,φ).
All binary relations are interpreted through the common Structure API. -/
structure IsRectangleStructure
    (d : RawDatum G C) (A : Structure (rectangleLanguage C) V) : Prop where
  parts_equiv : Equivalence (partRel A)
  raw_only_cross :
    ∀ (c : C) (x y : V), rawRel A c x y → ¬partRel A x y
  cross_unique :
    ∀ (x y : V), ¬partRel A x y → ∃! c : C, rawRel A c x y
  reverse :
    ∀ (c : C) (x y : V),
      rawRel A c x y ↔ rawRel A (d.reverse c) y x
  rectangle :
    ∀ (x₀ x₁ y₀ y₁ : V),
      partRel A x₀ x₁ → partRel A y₀ y₁ →
      ∀ (c₀₀ c₀₁ c₁₀ c₁₁ : C),
        rawRel A c₀₀ x₀ y₀ →
        rawRel A c₀₁ x₀ y₁ →
        rawRel A c₁₀ x₁ y₀ →
        rawRel A c₁₁ x₁ y₁ →
        (d.phi c₀₀)⁻¹ * d.phi c₀₁ =
          (d.phi c₁₀)⁻¹ * d.phi c₁₁

namespace IsRectangleStructure

variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) V}

/-- An existing colour edge is always between two different E-parts. -/
theorem no_raw_loops (h : IsRectangleStructure d A)
    (c : C) (x : V) : ¬rawRel A c x x := by
  intro hc
  exact h.raw_only_cross c x x hc (h.parts_equiv.refl x)

/-- Reverse edges have exactly the involuted raw colour. -/
theorem reverse_of_raw (h : IsRectangleStructure d A)
    {c : C} {x y : V} (hc : rawRel A c x y) :
    rawRel A (d.reverse c) y x :=
  (h.reverse c x y).mp hc

/-- The canonical quotient relation giving part imaginaries. -/
def partSetoid (h : IsRectangleStructure d A) : Setoid V where
  r := partRel A
  iseqv := h.parts_equiv

end IsRectangleStructure

end SemigenericEPPA
