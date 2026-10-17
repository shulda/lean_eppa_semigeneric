import SemigenericEPPA.Structure.OnePointEffective
import SemigenericEPPA.Algebra.SamePartRows

/-!
# Two new vertices in the same old E-part

This file discharges the remaining nontrivial local rectangle case of
one-point strong amalgamation. The two independently added vertices
may attach to the SAME old part P. For every different old part Q,
their two new rows must have the same horizontal displacement, and
dually their two new columns must have compatible vertical data.

Both facts follow from their individual R3 laws and the existing
rank-one append-two-rows / append-two-columns theorems. In particular
the proof does not incorrectly assume that the new vertices have
the same raw/effective colours.

Also, attachments may be transported between old representatives
of the same E-part; no transversal choice is hidden.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- If a new vertex is E-related to one old representative, it is
E-related to every other representative of that old part. -/
theorem onePoint_transfer_attachment
    (D : EffectiveGeometry s V)
    (L : OnePointEffectiveExtension D)
    (a b : V)
    (ha : L.geometry.part none (some a))
    (hab : D.part a b) :
    L.geometry.part none (some b) :=
  L.geometry.part.iseqv.trans ha ((L.old_part a b).2 hab)

/-- The two new vertices lie in the same old E-part P. Their
separately prescribed rows toward another old part Q jointly
satisfy every rectangle, including the new-row/new-row ones. -/
theorem onePoint_sameOldPart_rows
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (p q : V)
    (hLp : L.geometry.part none (some p))
    (hRp : R.geometry.part none (some p))
    (hpq : ¬D.part p q) :
    RectangleLaw
      (appendTwoRows
        (effectivePartMatrix D p q)
        (fun y => L.geometry.F none (some y.val))
        (fun y => R.geometry.F none (some y.val))) := by
  exact appendTwoRows_rectangle
    (effectivePartMatrix D p q)
    (effectivePartMatrix_rectangle D p q hpq)
    (fun y => L.geometry.F none (some y.val))
    (fun y => R.geometry.F none (some y.val))
    (effectivePartAnchor D p) (effectivePartAnchor D q)
    (onePoint_newRowCompatible D L p q hLp hpq)
    (onePoint_newRowCompatible D R p q hRp hpq)

/-- Concrete horizontal displacement identity for the two new
vertices in the same part, with NO assumption on their raw labels. -/
theorem onePoint_sameOldPart_row_displacement
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (p q : V)
    (hLp : L.geometry.part none (some p))
    (hRp : R.geometry.part none (some p))
    (hpq : ¬D.part p q)
    (a b : EffectivePartAt D q) :
    (L.geometry.F none (some a.val))⁻¹ *
      L.geometry.F none (some b.val) =
    (R.geometry.F none (some a.val))⁻¹ *
      R.geometry.F none (some b.val) := by
  have h := onePoint_sameOldPart_rows D L R p q hLp hRp hpq
    (Sum.inr false) (Sum.inr true) a b
  exact h

/-- Dually, the two independently new vertices attach to the same
old part Q and their columns towards an old part P satisfy EVERY
new-column/new-column rectangle. -/
theorem onePoint_sameOldPart_columns
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (p q : V)
    (hLq : L.geometry.part none (some q))
    (hRq : R.geometry.part none (some q))
    (hpq : ¬D.part p q) :
    RectangleLaw
      (appendTwoColumns
        (effectivePartMatrix D p q)
        (fun x => L.geometry.F (some x.val) none)
        (fun x => R.geometry.F (some x.val) none)) := by
  exact appendTwoColumns_rectangle
    (effectivePartMatrix D p q)
    (effectivePartMatrix_rectangle D p q hpq)
    (fun x => L.geometry.F (some x.val) none)
    (fun x => R.geometry.F (some x.val) none)
    (effectivePartAnchor D p) (effectivePartAnchor D q)
    (onePoint_newColumnCompatible D L p q hLq hpq)
    (onePoint_newColumnCompatible D R p q hRq hpq)

/-- The new columns also have the exact noncommutative vertical
displacement identity needed for R3. -/
theorem onePoint_sameOldPart_column_displacement
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (p q : V)
    (hLq : L.geometry.part none (some q))
    (hRq : R.geometry.part none (some q))
    (hpq : ¬D.part p q)
    (a b : EffectivePartAt D p) :
    (L.geometry.F (some a.val) none)⁻¹ *
      R.geometry.F (some a.val) none =
    (L.geometry.F (some b.val) none)⁻¹ *
      R.geometry.F (some b.val) none := by
  have h := onePoint_sameOldPart_columns D L R p q hLq hRq hpq
    a b (Sum.inr false) (Sum.inr true)
  exact h

/-- Same-part compatibility needs NO shared choice of old anchor:
the left and right new vertices can initially be attached using
different representatives in the same old equivalence class. -/
theorem onePoint_sameOldPart_rows_unanchored
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (p p' q : V)
    (hLp : L.geometry.part none (some p))
    (hRp' : R.geometry.part none (some p'))
    (hpp' : D.part p p')
    (hpq : ¬D.part p q) :
    RectangleLaw
      (appendTwoRows
        (effectivePartMatrix D p q)
        (fun y => L.geometry.F none (some y.val))
        (fun y => R.geometry.F none (some y.val))) := by
  have hRp : R.geometry.part none (some p) :=
    onePoint_transfer_attachment D R p' p hRp'
      (D.part.iseqv.symm hpp')
  exact onePoint_sameOldPart_rows D L R p q hLp hRp hpq

end SemigenericEPPA
