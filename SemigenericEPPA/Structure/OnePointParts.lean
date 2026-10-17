import Mathlib.Data.Setoid.Basic

/-!
# Exact strong amalgamation of one-point equivalence extensions

Two equivalence relations on A + {x} and A + {y} which agree on A
have a strong amalgam on A + {x,y}: both new vertices remain distinct,
and the two equivalence relations are reproduced exactly.

This formalizes the equivalence-part component of the one-point SAP
proof; it does not yet construct raw cross-part colours.
-/

namespace SemigenericEPPA

universe u

variable {V : Type u} (E : Setoid V)

/-- An equivalence relation on Option V whose restriction to V is E. -/
structure OnePointPartExtension where
  rel : Setoid (Option V)
  old_iff : ∀ a b : V, rel (some a) (some b) ↔ E a b

namespace OnePointPartExtension

variable {E}
variable (e : OnePointPartExtension E)

/-- The old E-class to which the new point attaches, if any. -/
noncomputable def attachment : Option (Quotient E) :=
  if h : ∃ a : V, e.rel none (some a)
  then some (Quotient.mk E (Classical.choose h))
  else none

/-- A new point is related to an old point exactly when the
attachment class equals that old point's quotient class. -/
theorem rel_none_some_iff_attachment (a : V) :
    e.rel none (some a) ↔
      e.attachment = some (Quotient.mk E a) := by
  classical
  by_cases hex : ∃ b : V, e.rel none (some b)
  · have hb : e.rel none (some (Classical.choose hex)) :=
      Classical.choose_spec hex
    constructor
    · intro ha
      have hold : e.rel (some (Classical.choose hex)) (some a) :=
        e.rel.iseqv.trans (e.rel.iseqv.symm hb) ha
      have hclass : Quotient.mk E (Classical.choose hex) =
          Quotient.mk E a :=
        Quotient.sound ((e.old_iff _ _).mp hold)
      simpa [attachment, hex] using congrArg some hclass
    · intro ha
      have hclass : Quotient.mk E (Classical.choose hex) =
          Quotient.mk E a := by
        simpa [attachment, hex] using ha
      exact e.rel.iseqv.trans hb
        ((e.old_iff _ _).mpr (Quotient.exact hclass))
  · constructor
    · intro ha
      exact (hex ⟨a, ha⟩).elim
    · intro ha
      simp [attachment, hex] at ha

/-- Labels for old quotient classes and (up to two) fresh classes. -/
abbrev PartLabel := (Quotient E) ⊕ Bool

/-- Class index of a one-point extension. The fresh label matters
only when the new vertex has no old-class attachment. -/
noncomputable def index (fresh : Bool) : Option V → PartLabel E
  | some a => Sum.inl (Quotient.mk E a)
  | none =>
      match e.attachment with
      | some cls => Sum.inl cls
      | none => Sum.inr fresh

private theorem index_none_some_iff (fresh : Bool) (a : V) :
    e.rel none (some a) ↔
      e.index fresh none = e.index fresh (some a) := by
  constructor
  · intro ha
    have hatt := (e.rel_none_some_iff_attachment a).mp ha
    simp [index, hatt]
  · intro hi
    have hatt : e.attachment = some (Quotient.mk E a) := by
      cases hs : e.attachment with
      | none =>
          simp [index, hs] at hi
      | some cls =>
          have hc : cls = Quotient.mk E a := by
            simpa [index, hs] using hi
          simpa [hs, hc]
    exact (e.rel_none_some_iff_attachment a).mpr hatt

/-- The original equivalence relation is the kernel of index. -/
theorem rel_iff_index (fresh : Bool) (x y : Option V) :
    e.rel x y ↔ e.index fresh x = e.index fresh y := by
  cases x with
  | none =>
    cases y with
    | none =>
      constructor
      · intro _
        rfl
      · intro _
        exact e.rel.iseqv.refl none
    | some b =>
      exact e.index_none_some_iff fresh b
  | some a =>
    cases y with
    | none =>
      constructor
      · intro h
        exact ((e.index_none_some_iff fresh a).mp
          (e.rel.iseqv.symm h)).symm
      · intro h
        exact e.rel.iseqv.symm
          ((e.index_none_some_iff fresh a).mpr h.symm)
    | some b =>
      constructor
      · intro h
        have he : E a b := (e.old_iff a b).mp h
        change (Sum.inl (Quotient.mk E a) : PartLabel E) =
          Sum.inl (Quotient.mk E b)
        exact congrArg Sum.inl (Quotient.sound he)
      · intro h
        have hclass : Quotient.mk E a = Quotient.mk E b := by
          simpa only [index, Sum.inl.injEq] using h
        exact (e.old_iff a b).mpr (Quotient.exact hclass)

end OnePointPartExtension

/-- Common old carrier, together with two genuinely distinct new points. -/
abbrev TwoPointCarrier (V : Type u) := V ⊕ Bool

/-- Inclusion of the first one-point carrier. -/
def firstOnePoint : Option V → TwoPointCarrier V
  | some a => Sum.inl a
  | none => Sum.inr false

/-- Inclusion of the second one-point carrier. -/
def secondOnePoint : Option V → TwoPointCarrier V
  | some a => Sum.inl a
  | none => Sum.inr true

theorem firstOnePoint_injective : Function.Injective (firstOnePoint (V := V)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [firstOnePoint]

theorem secondOnePoint_injective :
    Function.Injective (secondOnePoint (V := V)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [secondOnePoint]

theorem new_vertices_distinct :
    firstOnePoint (V := V) none ≠ secondOnePoint (V := V) none := by
  simp [firstOnePoint, secondOnePoint]

/-- The two E-partitions glue by canonical labels. -/
noncomputable def combinedPartIndex
    (l r : OnePointPartExtension E) :
    TwoPointCarrier V → (Quotient E) ⊕ Bool
  | Sum.inl a => Sum.inl (Quotient.mk E a)
  | Sum.inr false => l.index false none
  | Sum.inr true => r.index true none

/-- The strong amalgam of the equivalence relations is equality of
their canonical part labels. -/
noncomputable def amalgamPartSetoid
    (l r : OnePointPartExtension E) : Setoid (TwoPointCarrier V) where
  r x y := combinedPartIndex E l r x = combinedPartIndex E l r y
  iseqv := ⟨fun _ => rfl, fun _ _ => Eq.symm, fun _ _ _ => Eq.trans⟩

theorem combinedPartIndex_first
    (l r : OnePointPartExtension E) (a : Option V) :
    combinedPartIndex E l r (firstOnePoint a) = l.index false a := by
  cases a <;> rfl

theorem combinedPartIndex_second
    (l r : OnePointPartExtension E) (a : Option V) :
    combinedPartIndex E l r (secondOnePoint a) = r.index true a := by
  cases a <;> rfl

/-- Exact restriction to the first extension. -/
theorem amalgamPart_first_iff
    (l r : OnePointPartExtension E) (a b : Option V) :
    (amalgamPartSetoid E l r) (firstOnePoint a) (firstOnePoint b) ↔
      l.rel a b := by
  change combinedPartIndex E l r (firstOnePoint a) =
    combinedPartIndex E l r (firstOnePoint b) ↔ l.rel a b
  rw [combinedPartIndex_first E l r a, combinedPartIndex_first E l r b]
  exact (l.rel_iff_index false a b).symm

/-- Exact restriction to the second extension. -/
theorem amalgamPart_second_iff
    (l r : OnePointPartExtension E) (a b : Option V) :
    (amalgamPartSetoid E l r) (secondOnePoint a) (secondOnePoint b) ↔
      r.rel a b := by
  change combinedPartIndex E l r (secondOnePoint a) =
    combinedPartIndex E l r (secondOnePoint b) ↔ r.rel a b
  rw [combinedPartIndex_second E l r a, combinedPartIndex_second E l r b]
  exact (r.rel_iff_index true a b).symm

/-- No two previously different base parts are merged. -/
theorem amalgamPart_old_iff
    (l r : OnePointPartExtension E) (a b : V) :
    (amalgamPartSetoid E l r) (Sum.inl a) (Sum.inl b) ↔ E a b := by
  change (Sum.inl (Quotient.mk E a) : (Quotient E) ⊕ Bool) =
    Sum.inl (Quotient.mk E b) ↔ E a b
  simp only [Sum.inl.injEq, Quotient.eq]

end SemigenericEPPA
