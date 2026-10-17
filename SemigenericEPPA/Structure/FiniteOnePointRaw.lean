import SemigenericEPPA.Structure.OnePointRawExact
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Basic

/-!
# Finite one-point RAW strong amalgamation with no order hypothesis

The raw-fibre extension construction orients previously uncoloured
unordered cross-part edges using an auxiliary linear order.
A finite carrier always admits such an order, with no order in the
original relational language. We choose one noncomputably via an
equivalence with Fin n and prove the strong raw one-point SAP theorem
for arbitrary finite common base V, with NO extra order hypothesis.

In particular neither s(1)=1 nor a self-reversing raw colour is
assumed. The old-side raw colours are preserved and reflected exactly.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

/-- Any fintype admits a chosen linear order. This is an auxiliary
proof device: it is NOT added to the language of the structure. -/
noncomputable def finiteAuxiliaryLinearOrder (T : Type u)
    [Fintype T] : LinearOrder T :=
  LinearOrder.lift' (Fintype.equivFin T) (Fintype.equivFin T).injective

variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}
variable {D : EffectiveGeometry d.s V}
variable {L R : OnePointEffectiveExtension D}

/-- A finite common base and two compatible complete raw one-point
extensions have a strong raw one-point amalgam in the exact R1--R3
language. All E-relations and all P_c predicates on both sides are
preserved and reflected; the two new vertices remain distinct in
the canonical carrier V ⊕ Bool.

No linear ordering of the finite input structure is assumed. -/
theorem finite_raw_onePoint_strong_amalgamation
    [Fintype V]
    (A : OnePointRawColouring (d := d) D L)
    (B : OnePointRawColouring (d := d) D R)
    (hAgree : AgreeOnOldRaw A B) :
    ∃ S : Structure (rectangleLanguage C) (TwoPointCarrier V),
      IsRectangleStructure d S ∧
      (∀ x y : Option V,
        partRel S (firstOnePoint x) (firstOnePoint y) ↔
          L.geometry.part x y) ∧
      (∀ x y : Option V,
        partRel S (secondOnePoint x) (secondOnePoint y) ↔
          R.geometry.part x y) ∧
      (∀ c : C, ∀ x y : Option V,
        rawRel S c (firstOnePoint x) (firstOnePoint y) ↔
          A.colour x y = some c) ∧
      (∀ c : C, ∀ x y : Option V,
        rawRel S c (secondOnePoint x) (secondOnePoint y) ↔
          B.colour x y = some c) := by
  letI : LinearOrder (TwoPointCarrier V) :=
    finiteAuxiliaryLinearOrder (TwoPointCarrier V)
  exact raw_onePoint_strong_amalgamation A B hAgree

end SemigenericEPPA
