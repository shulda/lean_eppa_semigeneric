import SemigenericEPPA.Classification.DisplacementTranslations
import Mathlib.Data.Quot

/-!
# General rectangle laws: displacement and colour quotients

This is the algebraic core of the *converse* appendix. Starting with a
reversal-invariant predicate P on raw 2+2 rectangles and the TWO elementary
consequences of SAP (row amalgamation and corner completion), we construct a
displacement system on the quotient of raw colours by their invisible
distinctions.

The extraction of the two consequences from literal strong amalgamation is
a separate structural task, not an axiom of this file or an EPPA theorem.
-/

namespace SemigenericEPPA.Classification

universe u

/-- An arbitrary predicate on rectangles respecting all three
isomorphisms of a 2+2 rectangle (including starred transpose). -/
structure RectangleRule (C : Type u) where
  reverse : C → C
  reverse_involutive : ∀ c, reverse (reverse c) = c
  allowed : C → C → C → C → Prop
  row_swap : ∀ a b c d,
    allowed a b c d ↔ allowed c d a b
  col_swap : ∀ a b c d,
    allowed a b c d ↔ allowed b a d c
  starred_transpose : ∀ a b c d,
    allowed a b c d ↔
      allowed (reverse a) (reverse c) (reverse b) (reverse d)

/-- First elementary SAP consequence, extracted by amalgamating
two new row vertices over a shared old row. -/
def RectangleRule.HasRowAmalgamation {C : Type u} (R : RectangleRule C) : Prop :=
  ∀ a b c d e f, R.allowed a b c d →
    R.allowed a b e f → R.allowed c d e f

/-- Second elementary SAP consequence, extracted by amalgamating
the two independent ways to add the fourth rectangle corner. -/
def RectangleRule.HasCornerCompletion {C : Type u} (R : RectangleRule C) : Prop :=
  ∀ a b c, ∃ d, R.allowed a b c d

namespace RectangleRule

variable {C : Type u} (R : RectangleRule C)
variable (hrow : R.HasRowAmalgamation)
variable (hcorner : R.HasCornerCompletion)

/-- An allowed rectangle is precisely equality of two row
displacements. These are equivalence classes thanks to row
amalgamation and corner completion. -/
def rowSetoid : Setoid (C × C) where
  r p q := R.allowed p.1 p.2 q.1 q.2
  iseqv := by
    constructor
    · rintro ⟨a, b⟩
      obtain ⟨d, h⟩ := hcorner a b a
      have h' : R.allowed a d a b := (R.row_swap a b a d).mp h
      exact hrow a d a b a b h' h'
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      exact (R.row_swap a b c d).mp h
    · rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ h₁ h₂
      have h₁' : R.allowed c d a b := (R.row_swap a b c d).mp h₁
      exact hrow c d a b e f h₁' h₂

/-- Canonical equivalence classes of pairwise colour displacements. -/
abbrev Displacement := Quotient (R.rowSetoid hrow hcorner)

/-- The class of the row (a,b). -/
def displacement (a b : C) : R.Displacement hrow hcorner :=
  Quotient.mk (R.rowSetoid hrow hcorner) (a, b)

/-- Definitional quotient correspondence. -/
theorem displacement_eq_iff (a b c d : C) :
    R.displacement hrow hcorner a b =
      R.displacement hrow hcorner c d ↔
      R.allowed a b c d := by
  exact Quotient.eq

/-- All diagonal displacements coincide. -/
theorem displacement_diagonal (a b : C) :
    R.displacement hrow hcorner a a =
      R.displacement hrow hcorner b b := by
  have h : R.allowed (R.reverse a) (R.reverse b)
      (R.reverse a) (R.reverse b) :=
    (R.rowSetoid hrow hcorner).iseqv.refl
      (R.reverse a, R.reverse b)
  have ht := (R.starred_transpose
    (R.reverse a) (R.reverse b)
    (R.reverse a) (R.reverse b)).mp h
  apply (R.displacement_eq_iff hrow hcorner a a b b).mpr
  simpa only [R.reverse_involutive] using ht

/-- The key cancellation identity (A.8): equality of displacements
based at one column is independent of that column. -/
theorem same_second_independent (a b c d : C) :
    (R.displacement hrow hcorner a c =
      R.displacement hrow hcorner b c) ↔
    (R.displacement hrow hcorner a d =
      R.displacement hrow hcorner b d) := by
  calc
    (R.displacement hrow hcorner a c =
      R.displacement hrow hcorner b c) ↔
      (R.displacement hrow hcorner (R.reverse a) (R.reverse b) =
        R.displacement hrow hcorner (R.reverse c) (R.reverse c)) := by
          rw [R.displacement_eq_iff, R.displacement_eq_iff]
          exact R.starred_transpose a c b c
    _ ↔ (R.displacement hrow hcorner (R.reverse a) (R.reverse b) =
        R.displacement hrow hcorner (R.reverse d) (R.reverse d)) := by
          rw [R.displacement_diagonal hrow hcorner (R.reverse c) (R.reverse d)]
    _ ↔ (R.displacement hrow hcorner a d =
      R.displacement hrow hcorner b d) := by
        rw [R.displacement_eq_iff, R.displacement_eq_iff]
        exact (R.starred_transpose a d b d).symm

/-- Raw colours indistinguishable to all right-based displacements. -/
def colourSetoid : Setoid C where
  r a b := ∀ c, R.displacement hrow hcorner a c =
    R.displacement hrow hcorner b c
  iseqv := by
    constructor
    · intro a c
      rfl
    · intro a b h c
      exact (h c).symm
    · intro a b c h₁ h₂ d
      exact (h₁ d).trans (h₂ d)

/-- Equality in ONE right coordinate already establishes equality
in all right coordinates, hence colour equivalence. -/
theorem colour_rel_of_one (a b c : C)
    (h : R.displacement hrow hcorner a c =
      R.displacement hrow hcorner b c) :
    (R.colourSetoid hrow hcorner).Rel a b := by
  intro d
  exact (R.same_second_independent hrow hcorner a b c d).mp h

/-- The displacement map respects colour equivalence in its
second coordinate, using column interchange. -/
theorem displacement_respects_second (a b b' : C)
    (h : (R.colourSetoid hrow hcorner).Rel b b') :
    R.displacement hrow hcorner a b =
      R.displacement hrow hcorner a b' := by
  have hp : R.allowed b a b' a :=
    (R.displacement_eq_iff hrow hcorner b a b' a).mp (h a)
  exact (R.displacement_eq_iff hrow hcorner a b a b').mpr
    ((R.col_swap b a b' a).mp hp)

/-- Reversal descends to the quotient palette. -/
theorem colour_rel_reverse (a b : C)
    (h : (R.colourSetoid hrow hcorner).Rel a b) :
    (R.colourSetoid hrow hcorner).Rel (R.reverse a) (R.reverse b) := by
  have hp : R.allowed a b b b :=
    (R.displacement_eq_iff hrow hcorner a b b b).mp (h b)
  have hs : R.allowed (R.reverse a) (R.reverse b)
      (R.reverse b) (R.reverse b) :=
    (R.starred_transpose a b b b).mp hp
  have heq : R.displacement hrow hcorner (R.reverse a) (R.reverse b) =
      R.displacement hrow hcorner (R.reverse b) (R.reverse b) :=
    (R.displacement_eq_iff hrow hcorner
      (R.reverse a) (R.reverse b) (R.reverse b) (R.reverse b)).mpr hs
  exact R.colour_rel_of_one hrow hcorner
    (R.reverse a) (R.reverse b) (R.reverse b) heq

/-- The effective palette X = C/~ reconstructed from P. -/
abbrev Palette := Quotient (R.colourSetoid hrow hcorner)

/-- Both coordinates of q descend to the effective palette. -/
def paletteDisplacement
    (x y : R.Palette hrow hcorner) : R.Displacement hrow hcorner :=
  Quotient.liftOn₂ x y (fun a b => R.displacement hrow hcorner a b)
    (by
      intro a b a' b' ha hb
      exact (ha b).trans
        (R.displacement_respects_second hrow hcorner a' b b' hb))

@[simp] theorem paletteDisplacement_mk (a b : C) :
    R.paletteDisplacement hrow hcorner
      (Quotient.mk _ a) (Quotient.mk _ b) =
      R.displacement hrow hcorner a b := rfl

/-- The raw reversal induces an involution on the effective palette. -/
def paletteReverse (x : R.Palette hrow hcorner) :
    R.Palette hrow hcorner :=
  Quotient.liftOn x (fun c => Quotient.mk _ (R.reverse c))
    (by
      intro a b h
      exact Quotient.sound (R.colour_rel_reverse hrow hcorner a b h))

@[simp] theorem paletteReverse_mk (a : C) :
    R.paletteReverse hrow hcorner (Quotient.mk _ a) =
      Quotient.mk _ (R.reverse a) := rfl

theorem paletteReverse_involutive (x : R.Palette hrow hcorner) :
    R.paletteReverse hrow hcorner
      (R.paletteReverse hrow hcorner x) = x := by
  refine Quotient.inductionOn x ?_
  intro a
  change (Quotient.mk _ (R.reverse (R.reverse a))) =
    (Quotient.mk _ a)
  rw [R.reverse_involutive]

/-- Every row of the descended displacement map is injective. -/
theorem palette_row_injective (x : R.Palette hrow hcorner) :
    Function.Injective (R.paletteDisplacement hrow hcorner x) := by
  refine Quotient.inductionOn x ?_
  intro a
  intro b b'
  refine Quotient.inductionOn b ?_
  intro u
  refine Quotient.inductionOn b' ?_
  intro v h
  apply Quotient.sound
  apply R.colour_rel_of_one hrow hcorner u v a
  have hp : R.allowed a u a v :=
    (R.displacement_eq_iff hrow hcorner a u a v).mp h
  exact (R.displacement_eq_iff hrow hcorner u a v a).mpr
    ((R.col_swap a u a v).mp hp)

/-- Corner completion makes every descended displacement row surjective. -/
theorem palette_row_surjective (x : R.Palette hrow hcorner) :
    Function.Surjective (R.paletteDisplacement hrow hcorner x) := by
  refine Quotient.inductionOn x ?_
  intro a i
  refine Quotient.inductionOn i ?_
  rintro ⟨u, v⟩
  obtain ⟨d, hd⟩ := hcorner u v a
  refine ⟨Quotient.mk _ d, ?_⟩
  change R.displacement hrow hcorner a d =
    R.displacement hrow hcorner u v
  exact (R.displacement_eq_iff hrow hcorner a d u v).mpr
    ((R.row_swap u v a d).mp hd)

/-- The diagonal remains constant after removing invisible colours. -/
theorem palette_diagonal (x y : R.Palette hrow hcorner) :
    R.paletteDisplacement hrow hcorner x x =
      R.paletteDisplacement hrow hcorner y y := by
  refine Quotient.inductionOn x ?_
  intro a
  refine Quotient.inductionOn y ?_
  intro b
  exact R.displacement_diagonal hrow hcorner a b

/-- Pasting descends verbatim to the quotient palette. -/
theorem palette_pasting (a b c d e f : R.Palette hrow hcorner)
    (h₁ : R.paletteDisplacement hrow hcorner a b =
      R.paletteDisplacement hrow hcorner c d)
    (h₂ : R.paletteDisplacement hrow hcorner a e =
      R.paletteDisplacement hrow hcorner c f) :
    R.paletteDisplacement hrow hcorner b e =
      R.paletteDisplacement hrow hcorner d f := by
  revert h₁ h₂
  refine Quotient.inductionOn a ?_
  intro a
  refine Quotient.inductionOn b ?_
  intro b
  refine Quotient.inductionOn c ?_
  intro c
  refine Quotient.inductionOn d ?_
  intro d
  refine Quotient.inductionOn e ?_
  intro e
  refine Quotient.inductionOn f ?_
  intro f h₁ h₂
  apply (R.displacement_eq_iff hrow hcorner b e d f).mpr
  have hp : R.allowed a b c d :=
    (R.displacement_eq_iff hrow hcorner a b c d).mp h₁
  have hq : R.allowed a e c f :=
    (R.displacement_eq_iff hrow hcorner a e c f).mp h₂
  have hs : R.allowed (R.reverse a) (R.reverse c)
      (R.reverse b) (R.reverse d) :=
    (R.starred_transpose a b c d).mp hp
  have ht : R.allowed (R.reverse a) (R.reverse c)
      (R.reverse e) (R.reverse f) :=
    (R.starred_transpose a e c f).mp hq
  have hu := hrow (R.reverse a) (R.reverse c)
    (R.reverse b) (R.reverse d)
    (R.reverse e) (R.reverse f) hs ht
  have hv := (R.starred_transpose (R.reverse b) (R.reverse d)
    (R.reverse e) (R.reverse f)).mp hu
  simpa only [R.reverse_involutive] using hv

/-- The abstract hypotheses needed for the regular-group
construction follow from row amalgamation and corner completion. -/
def toDisplacementSystem :
    DisplacementSystem
      (R.Palette hrow hcorner) (R.Displacement hrow hcorner) where
  q := R.paletteDisplacement hrow hcorner
  row_bijective := by
    intro a
    exact ⟨R.palette_row_injective hrow hcorner a,
      R.palette_row_surjective hrow hcorner a⟩
  diagonal := R.palette_diagonal hrow hcorner
  pasting := R.palette_pasting hrow hcorner

end RectangleRule
end SemigenericEPPA.Classification
