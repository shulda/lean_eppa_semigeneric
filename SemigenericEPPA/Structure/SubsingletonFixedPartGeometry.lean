import SemigenericEPPA.Structure.IndexedGauge
import Mathlib.Data.Fintype.Prod

/-!
# An explicit fixed equal-fibre effective geometry when G is trivial

In the singleton effective-colour sector the group-valued rectangle
constraints impose no conditions beyond E. Therefore the carrier
I × Fin M is an actual effective geometry with E precisely equality
of the class index I. Its total effective colour is the unique
element of G, irrespective of the affine reversal.

Crucially I and M are fixed before any later induced substructure,
partial map or group action. Each E-class has the same fibre Fin M.
This is the concrete effective geometry required by the safe
replicated-fibre group action (and later fixed raw cover).
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Subsingleton G]

/-- The literal indexed gauge on the fixed carrier I×Fin M. -/
noncomputable def subsingletonFixedPartGauge
    (s : AffineAntiInvolution G) (I : Type v) (M : ℕ) :
    IndexedGauge s (I × Fin M) I where
  label := Prod.fst
  skeleton := fun _ _ => 1
  skeleton_reverse := by
    intro i j hij
    exact Subsingleton.elim _ _
  vertexGauge := fun _ _ => 1

/-- Actual finite-fibre effective rectangle geometry on the
preselected carrier, rather than just a labelled equivalence. -/
noncomputable def subsingletonFixedPartGeometry
    (s : AffineAntiInvolution G) (I : Type v) (M : ℕ) :
    EffectiveGeometry s (I × Fin M) :=
  (subsingletonFixedPartGauge s I M).toEffectiveGeometry

@[simp] theorem subsingletonFixedPartGeometry_part
    (s : AffineAntiInvolution G) (I : Type v) (M : ℕ)
    (x y : I × Fin M) :
    (subsingletonFixedPartGeometry s I M).part x y ↔
      x.1 = y.1 :=
  Iff.rfl

/-- All group-valued colours on this geometry agree, even on
same-part dummy pairs. -/
theorem subsingletonFixedPartGeometry_colour
    (s : AffineAntiInvolution G) (I : Type v) (M : ℕ)
    (x y : I × Fin M) :
    (subsingletonFixedPartGeometry s I M).F x y = 1 :=
  Subsingleton.elim _ _

/-- The fixed carrier is finite whenever its class-index sort is. -/
theorem subsingletonFixedPartGeometry_finiteCarrier
    (s : AffineAntiInvolution G) (I : Type v) (M : ℕ)
    [Finite I] :
    Finite (I × Fin M) := by
  classical
  letI : Fintype I := Fintype.ofFinite _
  infer_instance

/-- The old canonical class labels, paired with ANY chosen injection
into the globally prechosen Fin M, give an induced effective
embedding; no old E-classes are accidentally identified. -/
def fixedSubsingletonOldMap
    {V : Type v} {s : AffineAntiInvolution G}
    (D : EffectiveGeometry s V)
    (M : ℕ) (j : V → Fin M) (x : V) :
    Quotient D.part × Fin M :=
  (Quotient.mk D.part x, j x)

theorem fixedSubsingletonOldMap_injective
    {V : Type v} {s : AffineAntiInvolution G}
    (D : EffectiveGeometry s V)
    (M : ℕ) (j : V → Fin M)
    (hj : Function.Injective j) :
    Function.Injective (fixedSubsingletonOldMap D M j) := by
  intro x y hxy
  exact hj (congrArg Prod.snd hxy)

theorem fixedSubsingletonOldMap_part
    {V : Type v} {s : AffineAntiInvolution G}
    (D : EffectiveGeometry s V)
    (M : ℕ) (j : V → Fin M) (x y : V) :
    (subsingletonFixedPartGeometry s (Quotient D.part) M).part
        (fixedSubsingletonOldMap D M j x)
        (fixedSubsingletonOldMap D M j y) ↔
      D.part x y := by
  change (Quotient.mk D.part x = Quotient.mk D.part y) ↔ D.part x y
  exact ⟨Quotient.exact, Quotient.sound⟩

theorem fixedSubsingletonOldMap_colour
    {V : Type v} {s : AffineAntiInvolution G}
    (D : EffectiveGeometry s V)
    (M : ℕ) (j : V → Fin M) (x y : V) :
    (subsingletonFixedPartGeometry s (Quotient D.part) M).F
        (fixedSubsingletonOldMap D M j x)
        (fixedSubsingletonOldMap D M j y) = D.F x y :=
  Subsingleton.elim _ _

end SemigenericEPPA
