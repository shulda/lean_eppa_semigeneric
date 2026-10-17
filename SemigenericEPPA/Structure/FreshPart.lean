import SemigenericEPPA.Structure.OnePointParts

/-!
# Fresh classes are singletons in the strong one-point amalgam

The canonical equivalence amalgam classifies each new point as either
attached to an old E-part or starting a fresh E-part. Since we keep
the two new fresh classes distinct, a fresh point's E-class contains
no other vertices of the amalgam.

This is precisely why, in the manuscript's one-point SAP proof, an
edge between two distinct new E-parts with at least one fresh part
has no new nontrivial rectangle constraints. It is the complement
of the forced-corner and same-old-part cases already isolated.

There are no assumptions on the size of the old carrier, its order,
raw colours, or the group G.
-/

namespace SemigenericEPPA

universe u

variable {V : Type u}

/-- If the first new point does not attach to any old E-class, its
class in the strong amalgam consists of that one vertex only. -/
theorem freshFirstPart_singleton (E : Setoid V)
    (l r : OnePointPartExtension E)
    (hfresh : l.attachment = none)
    (x : TwoPointCarrier V) :
    (amalgamPartSetoid E l r) x (firstOnePoint none) ↔
      x = firstOnePoint none := by
  constructor
  · intro hx
    cases x with
    | inl a =>
      change combinedPartIndex E l r (Sum.inl a) =
        combinedPartIndex E l r (Sum.inr false) at hx
      simp [combinedPartIndex, OnePointPartExtension.index, hfresh] at hx
    | inr b =>
      cases b with
      | false => rfl
      | true =>
        change combinedPartIndex E l r (Sum.inr true) =
          combinedPartIndex E l r (Sum.inr false) at hx
        cases hr : r.attachment with
        | none =>
          simp [combinedPartIndex, OnePointPartExtension.index,
            hfresh, hr] at hx
        | some cls =>
          simp [combinedPartIndex, OnePointPartExtension.index,
            hfresh, hr] at hx
  · intro h
    rw [h]

/-- The symmetric assertion for the second new point, likewise
including the case where both new points start fresh E-parts. -/
theorem freshSecondPart_singleton (E : Setoid V)
    (l r : OnePointPartExtension E)
    (hfresh : r.attachment = none)
    (x : TwoPointCarrier V) :
    (amalgamPartSetoid E l r) x (secondOnePoint none) ↔
      x = secondOnePoint none := by
  constructor
  · intro hx
    cases x with
    | inl a =>
      change combinedPartIndex E l r (Sum.inl a) =
        combinedPartIndex E l r (Sum.inr true) at hx
      simp [combinedPartIndex, OnePointPartExtension.index, hfresh] at hx
    | inr b =>
      cases b with
      | true => rfl
      | false =>
        change combinedPartIndex E l r (Sum.inr false) =
          combinedPartIndex E l r (Sum.inr true) at hx
        cases hl : l.attachment with
        | none =>
          simp [combinedPartIndex, OnePointPartExtension.index,
            hfresh, hl] at hx
        | some cls =>
          simp [combinedPartIndex, OnePointPartExtension.index,
            hfresh, hl] at hx
  · intro h
    rw [h]

/-- The two fresh-part singleton assertions can be applied
symmetrically to either vertex of an E-related pair. -/
theorem freshFirstPart_pair_eq (E : Setoid V)
    (l r : OnePointPartExtension E)
    (hfresh : l.attachment = none)
    (x y : TwoPointCarrier V)
    (hx : (amalgamPartSetoid E l r) x (firstOnePoint none))
    (hy : (amalgamPartSetoid E l r) y (firstOnePoint none)) :
    x = y := by
  have hxx := (freshFirstPart_singleton E l r hfresh x).mp hx
  have hyy := (freshFirstPart_singleton E l r hfresh y).mp hy
  exact hxx.trans hyy.symm

end SemigenericEPPA
