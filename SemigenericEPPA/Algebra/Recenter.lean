import SemigenericEPPA.Algebra.AffineReversal
import SemigenericEPPA.Algebra.Rectangle
import Mathlib.Tactic.Group

/-!
# Torsor-origin translation and the rectangle law

The manuscript's formulas on the same carrier:
  x ⊙ y = x * g₀⁻¹ * y,
  e' = g₀,
  inv'(x) = g₀ * x⁻¹ * g₀.

Group laws are proved explicitly before packaging a transported Group instance.
An affine reversal becomes an anti-homomorphism when g₀ is a fixed point.
The rectangle law is invariant for any origin g₀.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G]

/-- Multiplication translated so the identity is at origin. -/
def translatedMul (origin x y : G) : G :=
  x * origin⁻¹ * y

/-- Inversion for the translated multiplication. -/
def translatedInv (origin x : G) : G :=
  origin * x⁻¹ * origin

theorem translatedMul_assoc (origin x y z : G) :
    translatedMul origin (translatedMul origin x y) z =
      translatedMul origin x (translatedMul origin y z) := by
  unfold translatedMul
  group

@[simp] theorem translatedMul_one_left (origin x : G) :
    translatedMul origin origin x = x := by
  unfold translatedMul
  group

@[simp] theorem translatedMul_one_right (origin x : G) :
    translatedMul origin x origin = x := by
  unfold translatedMul
  group

theorem translatedMul_inv_left (origin x : G) :
    translatedMul origin (translatedInv origin x) x = origin := by
  unfold translatedMul translatedInv
  group

theorem translatedMul_inv_right (origin x : G) :
    translatedMul origin x (translatedInv origin x) = origin := by
  unfold translatedMul translatedInv
  group

/-- Right translation is a multiplication-preserving bijection from the old
group to its new-origin multiplication. -/
@[simp] theorem translatedMul_right_translate (origin x y : G) :
    translatedMul origin (x * origin) (y * origin) = (x * y) * origin := by
  unfold translatedMul
  group

/-- Affine reversal of the inverse of a fixed origin. -/
theorem AffineAntiInvolution.reverse_fixed_origin_inv
    (s : AffineAntiInvolution G) {origin : G}
    (hfix : s origin = origin) :
    s (origin⁻¹) = s 1 * origin⁻¹ * s 1 := by
  have hprod : s (origin⁻¹) * (s 1)⁻¹ * origin = s 1 := by
    have h := s.map_mul origin (origin⁻¹)
    simpa only [mul_inv_cancel, hfix] using h.symm
  calc
    s (origin⁻¹) =
        (s (origin⁻¹) * (s 1)⁻¹ * origin) * origin⁻¹ * s 1 := by group
    _ = s 1 * origin⁻¹ * s 1 := by rw [hprod]

/-- An affine reversal becomes a genuine anti-homomorphism in the
new-origin multiplication when the origin is fixed by reversal. -/
theorem AffineAntiInvolution.reverse_translatedMul
    (s : AffineAntiInvolution G) {origin : G}
    (hfix : s origin = origin) (x y : G) :
    s (translatedMul origin x y) =
      translatedMul origin (s y) (s x) := by
  unfold translatedMul
  rw [s.map_mul, s.map_mul, s.reverse_fixed_origin_inv hfix]
  group

/-- New horizontal displacement equals old displacement times origin on left. -/
def translatedDisplacement (origin a b : G) : G :=
  translatedMul origin (translatedInv origin a) b

theorem translatedDisplacement_eq (origin a b : G) :
    translatedDisplacement origin a b = origin * (a⁻¹ * b) := by
  unfold translatedDisplacement translatedMul translatedInv
  group

/-- Recentring leaves the exact rectangle law unchanged, with no origin
fixed-point or colour self-reversal assumption. -/
theorem rectangle_translated_iff
    {X : Type v} {Y : Type w} (origin : G) (F : X → Y → G) :
    (∀ x₀ x₁ y₀ y₁,
      translatedDisplacement origin (F x₀ y₀) (F x₀ y₁) =
        translatedDisplacement origin (F x₁ y₀) (F x₁ y₁)) ↔
    RectangleLaw F := by
  constructor
  · intro h x₀ x₁ y₀ y₁
    have heq := h x₀ x₁ y₀ y₁
    rw [translatedDisplacement_eq, translatedDisplacement_eq] at heq
    exact mul_left_cancel heq
  · intro h x₀ x₁ y₀ y₁
    rw [translatedDisplacement_eq, translatedDisplacement_eq]
    exact congrArg (fun z : G => origin * z) (h x₀ x₁ y₀ y₁)

/-- Original affine congruence expression a*g*t⁻¹*s(a). -/
def congruence (s : AffineAntiInvolution G) (a g : G) : G :=
  a * g * s.normalized a

@[simp] theorem congruence_one (s : AffineAntiInvolution G) (g : G) :
    congruence s 1 g = g := by
  simp [congruence]

theorem congruence_mul (s : AffineAntiInvolution G)
    (a b g : G) :
    congruence s (a * b) g = congruence s a (congruence s b g) := by
  unfold congruence
  rw [s.normalized_mul]
  group

/-- Recentered congruence agrees with original affine congruence. -/
theorem congruence_recenter
    (s : AffineAntiInvolution G) {origin : G}
    (hfix : s origin = origin) (a g : G) :
    translatedMul origin
      (translatedMul origin (a * origin) g) (s (a * origin)) =
      congruence s a g := by
  rw [s.map_mul, hfix]
  unfold translatedMul congruence AffineAntiInvolution.normalized
  group

end SemigenericEPPA
