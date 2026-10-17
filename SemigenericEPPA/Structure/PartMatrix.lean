import SemigenericEPPA.Structure.EffectiveColour
import SemigenericEPPA.Algebra.Gauge

/-!
# Rank-one effective matrices between literal E-parts

The abstract rectangle algebra is now applied to actual R1--R3 structures.
Given two vertices p,q in distinct E-classes, their parts are nonempty
subtypes, and the cross-part effective colours form a total matrix
F : PartAt(p) → PartAt(q) → G.

The resulting rank-one and gauge formulas are exactly manuscript (2.3)
and (2.5), with no commutativity assumption and no arbitrary colours on
pairs belonging to the same E-class.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {C : Type u} {V : Type v} {G : Type w} [Group G]
variable {d : RawDatum G C} {A : Structure (rectangleLanguage C) V}

/-- The concrete carrier of the E-class of p. It is nonempty, witnessed
by p itself (assuming the rectangle-structure axioms). -/
def PartAt (A : Structure (rectangleLanguage C) V) (p : V) : Type v :=
  { x : V // partRel A x p }

namespace IsRectangleStructure

/-- The anchor belongs to its own E-part. -/
def partAnchor (h : IsRectangleStructure d A) (p : V) : PartAt A p :=
  ⟨p, h.parts_equiv.refl p⟩

/-- Vertices of different anchored parts are always cross-part. -/
theorem cross_of_parts (h : IsRectangleStructure d A)
    {p q : V} (hpq : ¬partRel A p q)
    (x : PartAt A p) (y : PartAt A q) :
    ¬partRel A x.val y.val := by
  intro hxy
  apply hpq
  exact h.parts_equiv.trans
    (h.parts_equiv.trans (h.parts_equiv.symm x.property) hxy)
    y.property

/-- The complete effective colour matrix between two different parts. -/
noncomputable def betweenParts (h : IsRectangleStructure d A)
    (p q : V) (hpq : ¬partRel A p q) :
    PartAt A p → PartAt A q → G :=
  fun x y => h.chosenEffective x.val y.val (h.cross_of_parts hpq x y)

/-- Reverse the two parts: the opposite effective matrix is obtained
by the affine anti-involution, not by group inversion. -/
theorem betweenParts_reverse (h : IsRectangleStructure d A)
    (p q : V) (hpq : ¬partRel A p q)
    (x : PartAt A p) (y : PartAt A q) :
    (h.betweenParts q p (h.cross_symm hpq)) y x =
      d.s ((h.betweenParts p q hpq) x y) := by
  exact h.chosenEffective_reverse x.val y.val
    (h.cross_of_parts hpq x y)
    (h.cross_of_parts (h.cross_symm hpq) y x)

/-- The canonical matrix of two actual E-parts satisfies the full
noncommutative rectangle law. -/
theorem betweenParts_rectangle (h : IsRectangleStructure d A)
    (p q : V) (hpq : ¬partRel A p q) :
    RectangleLaw (h.betweenParts p q hpq) := by
  intro x₀ x₁ y₀ y₁
  have hx : partRel A x₀.val x₁.val :=
    h.parts_equiv.trans x₀.property (h.parts_equiv.symm x₁.property)
  have hy : partRel A y₀.val y₁.val :=
    h.parts_equiv.trans y₀.property (h.parts_equiv.symm y₁.property)
  exact h.chosenEffective_rectangle x₀.val x₁.val y₀.val y₁.val
    hx hy
    (h.cross_of_parts hpq x₀ y₀)
    (h.cross_of_parts hpq x₀ y₁)
    (h.cross_of_parts hpq x₁ y₀)
    (h.cross_of_parts hpq x₁ y₁)

/-- Equation (2.3) as a theorem about the actual colour structure,
with both anchors chosen from their own parts. -/
theorem betweenParts_factor (h : IsRectangleStructure d A)
    (p q : V) (hpq : ¬partRel A p q)
    (x : PartAt A p) (y : PartAt A q) :
    (h.betweenParts p q hpq) x y =
      (h.betweenParts p q hpq) x (h.partAnchor q) *
      ((h.betweenParts p q hpq) (h.partAnchor p) (h.partAnchor q))⁻¹ *
      (h.betweenParts p q hpq) (h.partAnchor p) y := by
  exact factor_of_rectangle (h.betweenParts p q hpq)
    (h.betweenParts_rectangle p q hpq)
    (h.partAnchor p) (h.partAnchor q) x y

/-- Every cross-part effective matrix is rank-one. -/
theorem betweenParts_rankOne (h : IsRectangleStructure d A)
    (p q : V) (hpq : ¬partRel A p q) :
    IsRankOne (h.betweenParts p q hpq) := by
  exact rankOne_of_rectangle (h.betweenParts p q hpq)
    (h.betweenParts_rectangle p q hpq)
    (h.partAnchor p) (h.partAnchor q)

/-- Equation (2.5): the anchored effective matrix is written in the
exact s(left) K⁻¹ right gauge convention of the manuscript. The first
gauge coordinate reads the REVERSED edge q→x, not x→q. -/
theorem betweenParts_gauge (h : IsRectangleStructure d A)
    (p q : V) (hpq : ¬partRel A p q)
    (x : PartAt A p) (y : PartAt A q) :
    (h.betweenParts p q hpq) x y =
      gaugeColour d.s
        ((h.betweenParts q p (h.cross_symm hpq)) (h.partAnchor q) x)
        ((h.betweenParts p q hpq) (h.partAnchor p) (h.partAnchor q))
        ((h.betweenParts p q hpq) (h.partAnchor p) y) := by
  have hreverse :
      (h.betweenParts p q hpq) x (h.partAnchor q) =
      d.s ((h.betweenParts q p (h.cross_symm hpq)) (h.partAnchor q) x) := by
    have hr := h.betweenParts_reverse p q hpq x (h.partAnchor q)
    calc
      (h.betweenParts p q hpq) x (h.partAnchor q) =
        d.s (d.s ((h.betweenParts p q hpq) x (h.partAnchor q))) :=
          (d.s.involutive _).symm
      _ = d.s ((h.betweenParts q p (h.cross_symm hpq))
          (h.partAnchor q) x) := by rw [← hr]
  calc
    (h.betweenParts p q hpq) x y =
      (h.betweenParts p q hpq) x (h.partAnchor q) *
        ((h.betweenParts p q hpq) (h.partAnchor p) (h.partAnchor q))⁻¹ *
        (h.betweenParts p q hpq) (h.partAnchor p) y :=
        h.betweenParts_factor p q hpq x y
    _ = gaugeColour d.s
        ((h.betweenParts q p (h.cross_symm hpq)) (h.partAnchor q) x)
        ((h.betweenParts p q hpq) (h.partAnchor p) (h.partAnchor q))
        ((h.betweenParts p q hpq) (h.partAnchor p) y) := by
      rw [hreverse]
      rfl

end IsRectangleStructure
end SemigenericEPPA
