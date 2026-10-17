import SemigenericEPPA.Structure.EffectiveGeometry
import SemigenericEPPA.Structure.OnePointParts
import SemigenericEPPA.Algebra.CornerAmalgamation

/-!
# Forced effective corner from two actual one-point extensions

We now connect the abstract rank-one corner lemma to the exact
effective geometry of two one-point extensions of the SAME base.

The two extensions have vertex types Option V, each with its own
new vertex none. The old E-relation and every old effective colour
are exactly reflected by both inclusions. If the new left vertex
attaches to an old E-part P and the new right vertex to a DISTINCT
old part Q, then R3 supplies the RowCompatible/ColumnCompatible
hypotheses of the previously verified algebraic corner lemma.

Consequently, the missing effective colour is forced, is independent
of anchor choices inside P and Q, and yields ALL rectangles on the
P×Q matrix extended by both vertices. No commutativity, finiteness,
raw-colour choices, or coherent-EPPA assumptions are involved.

This is the genuinely geometric old-part/old-part case of the
one-point SAP proof, not yet its global assembly over all E-parts.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- An effective one-point extension, restricting EXACTLY to the
original base geometry on all old vertices. -/
structure OnePointEffectiveExtension (D : EffectiveGeometry s V) where
  geometry : EffectiveGeometry s (Option V)
  old_part : ∀ a b : V,
    geometry.part (some a) (some b) ↔ D.part a b
  old_F : ∀ a b : V,
    geometry.F (some a) (some b) = D.F a b

namespace OnePointEffectiveExtension

variable {D : EffectiveGeometry s V}

/-- Each effective one-point extension induces the exact one-point
equivalence extension used by the part-amalgamation theorem. -/
def toPartExtension (L : OnePointEffectiveExtension D) :
    OnePointPartExtension D.part where
  rel := L.geometry.part
  old_iff := L.old_part

end OnePointEffectiveExtension

/-- The actual old vertices in an anchored E-part. -/
def EffectivePartAt (D : EffectiveGeometry s V) (p : V) : Type v :=
  { x : V // D.part x p }

/-- Every anchored part is inhabited by its anchor. -/
def effectivePartAnchor (D : EffectiveGeometry s V) (p : V) :
    EffectivePartAt D p :=
  ⟨p, D.part.iseqv.refl p⟩

/-- Cross-part effective colours between two anchored old E-parts. -/
def effectivePartMatrix
    (D : EffectiveGeometry s V) (p q : V) :
    EffectivePartAt D p → EffectivePartAt D q → G :=
  fun x y => D.F x.val y.val

/-- Distinct old E-parts remain disjoint at all of their vertices. -/
theorem effectivePart_cross
    (D : EffectiveGeometry s V) {p q : V}
    (hpq : ¬D.part p q)
    (x : EffectivePartAt D p) (y : EffectivePartAt D q) :
    ¬D.part x.val y.val := by
  intro hxy
  exact hpq
    (D.part.iseqv.trans
      (D.part.iseqv.symm x.property)
      (D.part.iseqv.trans hxy y.property))

/-- The base matrix between distinct old E-parts is rank-one. -/
theorem effectivePartMatrix_rectangle
    (D : EffectiveGeometry s V) (p q : V)
    (hpq : ¬D.part p q) :
    RectangleLaw (effectivePartMatrix D p q) := by
  intro x₀ x₁ y₀ y₁
  exact D.rectangle x₀.val x₁.val y₀.val y₁.val
    (D.part.iseqv.trans x₀.property (D.part.iseqv.symm x₁.property))
    (D.part.iseqv.trans y₀.property (D.part.iseqv.symm y₁.property))
    (effectivePart_cross D hpq x₀ y₀)

/-- When the left new vertex attaches to p's old E-part,
its whole row towards q's old E-part has exactly the
noncommutative horizontal displacement of the base matrix. -/
theorem onePoint_newRowCompatible
    (D : EffectiveGeometry s V)
    (L : OnePointEffectiveExtension D)
    (p q : V)
    (hnewp : L.geometry.part none (some p))
    (hpq : ¬D.part p q) :
    RowCompatible
      (effectivePartMatrix D p q)
      (fun y => L.geometry.F none (some y.val))
      (effectivePartAnchor D p) (effectivePartAnchor D q) := by
  intro y
  have hqy : L.geometry.part (some q) (some y.val) :=
    (L.old_part q y.val).2 (D.part.iseqv.symm y.property)
  have hcross : ¬L.geometry.part none (some q) := by
    intro hnewq
    have hpq' : L.geometry.part (some p) (some q) :=
      L.geometry.part.iseqv.trans
        (L.geometry.part.iseqv.symm hnewp) hnewq
    exact hpq ((L.old_part p q).1 hpq')
  have hr := L.geometry.rectangle
    none (some p) (some q) (some y.val) hnewp hqy hcross
  rw [L.old_F p q, L.old_F p y.val] at hr
  exact hr

/-- Dually, when the right new vertex attaches to q's old
E-part, its column across p's old E-part has exactly the
noncommutative vertical displacement of the base matrix. -/
theorem onePoint_newColumnCompatible
    (D : EffectiveGeometry s V)
    (R : OnePointEffectiveExtension D)
    (p q : V)
    (hnewq : R.geometry.part none (some q))
    (hpq : ¬D.part p q) :
    ColumnCompatible
      (effectivePartMatrix D p q)
      (fun x => R.geometry.F (some x.val) none)
      (effectivePartAnchor D p) (effectivePartAnchor D q) := by
  intro x
  have hxp : R.geometry.part (some x.val) (some p) :=
    (R.old_part x.val p).2 x.property
  have hqnew : R.geometry.part (some q) none :=
    R.geometry.part.iseqv.symm hnewq
  have hxq : ¬D.part x.val q := by
    intro h
    exact hpq
      (D.part.iseqv.trans (D.part.iseqv.symm x.property) h)
  have hcross : ¬R.geometry.part (some x.val) (some q) := by
    intro h
    exact hxq ((R.old_part x.val q).1 h)
  have hc := R.geometry.rectangle
    (some x.val) (some p) (some q) none hxp hqnew hcross
  rw [R.old_F x.val q, R.old_F p q] at hc
  exact hc

/-- The forced new-left/new-right effective colour between two
different old E-parts, in precisely the manuscript factor order. -/
def effectiveForcedCorner
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (p q : V) : G :=
  forcedCorner
    (effectivePartMatrix D p q)
    (fun y => L.geometry.F none (some y.val))
    (fun x => R.geometry.F (some x.val) none)
    (effectivePartAnchor D p) (effectivePartAnchor D q)

/-- The four kinds of entries between the two old E-parts and their
two attached new vertices form a complete rectangle matrix. -/
theorem onePoint_effectiveCorner_rectangle
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (p q : V)
    (hnewp : L.geometry.part none (some p))
    (hnewq : R.geometry.part none (some q))
    (hpq : ¬D.part p q) :
    RectangleLaw
      (extendCorner
        (effectivePartMatrix D p q)
        (fun y => L.geometry.F none (some y.val))
        (fun x => R.geometry.F (some x.val) none)
        (effectiveForcedCorner D L R p q)) := by
  exact forcedCorner_rectangle
    (effectivePartMatrix D p q)
    (effectivePartMatrix_rectangle D p q hpq)
    (fun y => L.geometry.F none (some y.val))
    (fun x => R.geometry.F (some x.val) none)
    (effectivePartAnchor D p) (effectivePartAnchor D q)
    (onePoint_newRowCompatible D L p q hnewp hpq)
    (onePoint_newColumnCompatible D R p q hnewq hpq)

/-- The value forced by the two real one-point extensions is
independent of the old anchors chosen in the respective E-parts. -/
theorem onePoint_effectiveCorner_anchor_independent
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (p q : V)
    (hnewp : L.geometry.part none (some p))
    (hnewq : R.geometry.part none (some q))
    (hpq : ¬D.part p q)
    (a : EffectivePartAt D p) (b : EffectivePartAt D q) :
    effectiveForcedCorner D L R p q =
      forcedCorner
        (effectivePartMatrix D p q)
        (fun y => L.geometry.F none (some y.val))
        (fun x => R.geometry.F (some x.val) none)
        a b := by
  exact forcedCorner_anchor_independent
    (effectivePartMatrix D p q)
    (effectivePartMatrix_rectangle D p q hpq)
    (fun y => L.geometry.F none (some y.val))
    (fun x => R.geometry.F (some x.val) none)
    (effectivePartAnchor D p) a
    (effectivePartAnchor D q) b
    (onePoint_newRowCompatible D L p q hnewp hpq)
    (onePoint_newColumnCompatible D R p q hnewq hpq)

end SemigenericEPPA
