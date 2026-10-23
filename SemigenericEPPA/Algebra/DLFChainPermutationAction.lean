import Mathlib.Algebra.Group.End
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Group

/-!
# The strict permutation action on finite F₂ edge chains

In the audited relative involution-killing cover, Q permutes the
edges of a finite graph and acts on the F₂ edge-chain space
C₁ = E→ZMod 2 by reindexing coefficients. To form
C₁ ⋊ Q correctly, we first certify the precise inverse-index
action and its multiplication order for potentially nonabelian Q.

For g in Q, define (g·c)(e) = c(ρ(g⁻¹)e). The action is strict:
1·c=c, (gh)·c=g·(h·c), and it distributes over sums.
The proof is independent of the graph endpoints, so that the
same API can later be reused for vertex chains C₀.

No semidirect product, parity obstruction, or dense locally finite
subgroup is asserted in this module.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v
variable {Q : Type u} [Group Q]
variable {E : Type v}

/-- Genuine left Q-action on F₂ coefficient functions, indexed
by the inverse edge permutation. -/
def chainPermutationAction
    (rho : Q →* Equiv.Perm E) (g : Q)
    (c : E → ZMod 2) : E → ZMod 2 :=
  fun e => c (rho g⁻¹ e)

@[simp] theorem chainPermutationAction_one
    (rho : Q →* Equiv.Perm E) (c : E → ZMod 2) :
    chainPermutationAction rho 1 c = c := by
  funext e
  simp [chainPermutationAction]

/-- Correct (noncommutative) order of composing the induced
action on edge-chain coefficients. -/
theorem chainPermutationAction_mul
    (rho : Q →* Equiv.Perm E) (g h : Q)
    (c : E → ZMod 2) :
    chainPermutationAction rho (g * h) c =
      chainPermutationAction rho g
        (chainPermutationAction rho h c) := by
  funext e
  change c (rho (g * h)⁻¹ e) =
    c (rho h⁻¹ (rho g⁻¹ e))
  rw [mul_inv_rev, map_mul]
  rfl

@[simp] theorem chainPermutationAction_zero
    (rho : Q →* Equiv.Perm E) (g : Q) :
    chainPermutationAction rho g (0 : E → ZMod 2) = 0 := by
  funext e
  rfl

/-- The coefficient action preserves F₂ addition pointwise. -/
theorem chainPermutationAction_add
    (rho : Q →* Equiv.Perm E) (g : Q)
    (c d : E → ZMod 2) :
    chainPermutationAction rho g (c + d) =
      chainPermutationAction rho g c +
        chainPermutationAction rho g d := by
  funext e
  rfl

/-- The inverse group element supplies the inverse chain
reindexing, not necessarily an order-two action. -/
theorem chainPermutationAction_inv_cancel
    (rho : Q →* Equiv.Perm E) (g : Q)
    (c : E → ZMod 2) :
    chainPermutationAction rho g⁻¹
      (chainPermutationAction rho g c) = c := by
  calc
    chainPermutationAction rho g⁻¹
        (chainPermutationAction rho g c) =
      chainPermutationAction rho (g⁻¹ * g) c :=
        (chainPermutationAction_mul rho g⁻¹ g c).symm
    _ = c := by simp

end RelativeDLF
end SemigenericEPPA
