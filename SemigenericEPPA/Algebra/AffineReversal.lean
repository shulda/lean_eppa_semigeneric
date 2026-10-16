import Mathlib.Algebra.Group.Defs

/-!
# Affine anti-involutions

The manuscript starts with an arbitrary affine anti-involution:
`s (x * y) = s y * (s 1)⁻¹ * s x`.
The factor `s 1` must not be silently replaced with the identity.
This module isolates the first noncommutative algebraic consequences.

No finiteness is needed for these calculations.
-/

namespace SemigenericEPPA

/-- An involutive affine anti-automorphism, in the exact manuscript convention. -/
structure AffineAntiInvolution (G : Type*) [Group G] where
  toFun : G → G
  involutive : ∀ x : G, toFun (toFun x) = x
  map_mul : ∀ x y : G,
    toFun (x * y) = toFun y * (toFun 1)⁻¹ * toFun x

namespace AffineAntiInvolution

variable {G : Type*} [Group G]

instance : CoeFun (AffineAntiInvolution G) (fun _ => G → G) :=
  ⟨AffineAntiInvolution.toFun⟩

/-- Normalizing the affine reversal by its value at the identity. -/
def normalized (s : AffineAntiInvolution G) (x : G) : G :=
  (s 1)⁻¹ * s x

@[simp] theorem normalized_one (s : AffineAntiInvolution G) :
    s.normalized 1 = 1 := by
  simp [normalized]

/-- The normalization is a genuine anti-homomorphism without assuming s(1)=1. -/
theorem normalized_mul (s : AffineAntiInvolution G) (x y : G) :
    s.normalized (x * y) = s.normalized y * s.normalized x := by
  change (s 1)⁻¹ * s (x * y) =
    ((s 1)⁻¹ * s y) * ((s 1)⁻¹ * s x)
  rw [s.map_mul]
  simp only [mul_assoc]

theorem injective (s : AffineAntiInvolution G) :
    Function.Injective s.toFun := by
  intro x y h
  calc
    x = s (s x) := (s.involutive x).symm
    _ = s (s y) := congrArg s.toFun h
    _ = y := s.involutive y

theorem surjective (s : AffineAntiInvolution G) :
    Function.Surjective s.toFun := by
  intro y
  exact ⟨s y, s.involutive y⟩

end AffineAntiInvolution
end SemigenericEPPA
