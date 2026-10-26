import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Tactic.Group

/-!
# Reconstructing a regular group from rectangle displacements

The abstract core of Appendix A: a displacement map with Latin rows, a
constant diagonal and the pasting identity determines a regular permutation
group. No group structure is assumed on the starting set.

The geometric argument that strong amalgamation produces these hypotheses
is deliberately separated from this algebraic reconstruction.
-/

namespace SemigenericEPPA.Classification

universe u v

/-- Abstract displacement data extracted from the rectangle predicate.
A row means the map b ↦ q(a,b). The "pasting" identity is the
starred-transpose cancellation law. -/
structure DisplacementSystem (X : Type u) (I : Type v) where
  q : X → X → I
  row_bijective : ∀ a, Function.Bijective (q a)
  diagonal : ∀ a b, q a a = q b b
  pasting : ∀ a b c d e f,
    q a b = q c d →
    q a e = q c f →
    q b e = q d f

namespace DisplacementSystem

variable {X : Type u} {I : Type v} (S : DisplacementSystem X I)

/-- Every anchored displacement row is an equivalence. -/
noncomputable def rowEquiv (a : X) : X ≃ I :=
  Equiv.ofBijective (S.q a) (S.row_bijective a)

/-- The unique transport mapping a row based at a onto a row based at c. -/
noncomputable def translation (a c : X) : Equiv.Perm X :=
  (S.rowEquiv a).trans (S.rowEquiv c).symm

theorem translation_q (a c x : X) :
    S.q c (S.translation a c x) = S.q a x := by
  change S.rowEquiv c (S.translation a c x) = S.rowEquiv a x
  simp [translation]

/-- A transport sending the first anchor to the second. -/
theorem translation_anchor (a c : X) :
    S.translation a c a = c := by
  apply (S.row_bijective c).1
  rw [S.translation_q]
  exact S.diagonal a c

/-- The starred-transpose/pasting identity makes all transports
preserve *every* displacement. -/
theorem translation_preserves (a c x y : X) :
    S.q (S.translation a c x) (S.translation a c y) = S.q x y := by
  exact (S.pasting a x c (S.translation a c x)
    y (S.translation a c y)
    (S.translation_q a c x).symm
    (S.translation_q a c y).symm).symm

/-- Any displacement-preserving permutation is determined by the
image of a single anchor. -/
theorem preserving_perm_eq_translation
    (f : Equiv.Perm X)
    (hf : ∀ x y, S.q (f x) (f y) = S.q x y) (a : X) :
    f = S.translation a (f a) := by
  apply Equiv.ext
  intro x
  apply (S.row_bijective (f a)).1
  calc
    S.q (f a) (f x) = S.q a x := hf a x
    _ = S.q (f a) (S.translation a (f a) x) :=
      (S.translation_q a (f a) x).symm

/-- The group of *all* displacement-preserving permutations, defined
without postulating a group structure on X. -/
def preservingGroup : Subgroup (Equiv.Perm X) where
  carrier := {f | ∀ x y, S.q (f x) (f y) = S.q x y}
  one_mem' := by
    intro x y
    rfl
  mul_mem' := by
    intro f g hf hg x y
    change S.q (f (g x)) (f (g y)) = S.q x y
    rw [hf (g x) (g y), hg x y]
  inv_mem' := by
    intro f hf x y
    change S.q (f.symm x) (f.symm y) = S.q x y
    have h := hf (f.symm x) (f.symm y)
    simpa using h.symm

/-- Every canonical translation belongs to the regular group. -/
noncomputable def translationElement (a c : X) : S.preservingGroup :=
  ⟨S.translation a c, S.translation_preserves a c⟩

/-- Coordinates relative to a chosen origin. -/
noncomputable def coordinate (e a : X) : S.preservingGroup :=
  S.translationElement e a

theorem coordinate_anchor (e a : X) :
    ((S.coordinate e a : S.preservingGroup) : Equiv.Perm X) e = a :=
  S.translation_anchor e a

/-- Evaluation at any anchor is injective on the preserving group. -/
theorem preserving_eval_injective (e : X) :
    Function.Injective
      (fun g : S.preservingGroup => ((g : Equiv.Perm X) e)) := by
  intro f g h
  apply Subtype.ext
  calc
    (f : Equiv.Perm X) =
      S.translation e ((f : Equiv.Perm X) e) :=
        S.preserving_perm_eq_translation f f.property e
    _ = S.translation e ((g : Equiv.Perm X) e) := by rw [h]
    _ = (g : Equiv.Perm X) :=
      (S.preserving_perm_eq_translation g g.property e).symm

/-- Evaluation is surjective as well: all vertices are attained by
the canonical translations. -/
theorem preserving_eval_surjective (e : X) :
    Function.Surjective
      (fun g : S.preservingGroup => ((g : Equiv.Perm X) e)) := by
  intro a
  exact ⟨S.coordinate e a, S.coordinate_anchor e a⟩

/-- The reconstructed group acts regularly, and the choice of an
origin identifies its torsor of points with the group itself. -/
noncomputable def coordinateEquiv (e : X) : X ≃ S.preservingGroup :=
  (Equiv.ofBijective
    (fun g : S.preservingGroup => ((g : Equiv.Perm X) e))
    ⟨S.preserving_eval_injective e, S.preserving_eval_surjective e⟩).symm

theorem coordinateEquiv_apply (e a : X) :
    S.coordinateEquiv e a = S.coordinate e a := by
  apply S.preserving_eval_injective e
  simp only [coordinateEquiv, Equiv.ofBijective_symm_apply]
  exact (S.coordinate_anchor e a).symm

/-- A displacement can be transported from any initial point a to c. -/
theorem displacement_iff_translation (a b c d : X) :
    S.q a b = S.q c d ↔ S.translation a c b = d := by
  constructor
  · intro h
    apply (S.row_bijective c).1
    calc
      S.q c (S.translation a c b) = S.q a b := S.translation_q a c b
      _ = S.q c d := h
  · intro h
    calc
      S.q a b = S.q c (S.translation a c b) :=
        (S.translation_q a c b).symm
      _ = S.q c d := by rw [h]

/-- Applying a group element to x is equivalent to multiplying
the group coordinate of x on the left. -/
theorem act_iff_mul_coordinate (e x y : X) (g : S.preservingGroup) :
    ((g : Equiv.Perm X) x = y) ↔
      g * S.coordinate e x = S.coordinate e y := by
  constructor
  · intro h
    apply S.preserving_eval_injective e
    change (g * S.coordinate e x : S.preservingGroup) = S.coordinate e y
    change ((g : Equiv.Perm X) *
      (S.translation e x)) e = (S.translation e y) e
    rw [Equiv.Perm.mul_apply, S.translation_anchor,
      S.translation_anchor]
    exact h
  · intro h
    have he := congrArg
      (fun k : S.preservingGroup => ((k : Equiv.Perm X) e)) h
    change ((g : Equiv.Perm X) *
      (S.translation e x)) e = (S.translation e y) e at he
    rw [Equiv.Perm.mul_apply, S.translation_anchor,
      S.translation_anchor] at he
    exact he

/-- The translation a ↦ c has group coordinate c * a⁻¹. -/
theorem translationElement_eq_coordinates (e a c : X) :
    S.translationElement a c =
      S.coordinate e c * (S.coordinate e a)⁻¹ := by
  have h :
      S.translationElement a c * S.coordinate e a =
        S.coordinate e c :=
    (S.act_iff_mul_coordinate e a c (S.translationElement a c)).mp
      (S.translation_anchor a c)
  calc
    S.translationElement a c =
      (S.translationElement a c * S.coordinate e a) *
        (S.coordinate e a)⁻¹ := by group
    _ = S.coordinate e c * (S.coordinate e a)⁻¹ := by rw [h]

/-- Exact reconstruction of the displacement law as the usual
noncommutative quotient of group coordinates. -/
theorem displacement_iff_group_difference (e a b c d : X) :
    S.q a b = S.q c d ↔
      (S.coordinate e a)⁻¹ * S.coordinate e b =
        (S.coordinate e c)⁻¹ * S.coordinate e d := by
  rw [S.displacement_iff_translation a b c d]
  rw [S.act_iff_mul_coordinate e b d (S.translationElement a c)]
  rw [S.translationElement_eq_coordinates e a c]
  constructor
  · intro h
    calc
      (S.coordinate e a)⁻¹ * S.coordinate e b =
        (S.coordinate e c)⁻¹ *
          (S.coordinate e c *
            ((S.coordinate e a)⁻¹ * S.coordinate e b)) := by group
      _ = (S.coordinate e c)⁻¹ * S.coordinate e d := by
        rw [← mul_assoc, h]
  · intro h
    calc
      S.coordinate e c * (S.coordinate e a)⁻¹ * S.coordinate e b =
        S.coordinate e c *
          ((S.coordinate e c)⁻¹ * S.coordinate e d) := by
            rw [mul_assoc, h]
      _ = S.coordinate e d := by group

end DisplacementSystem

end SemigenericEPPA.Classification
