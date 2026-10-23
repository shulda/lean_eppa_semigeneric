import SemigenericEPPA.Algebra.DLFChainPermutationAction
import Mathlib.Algebra.Group.Defs

/-!
# Actual semidirect group of finite F₂ edge chains by an arbitrary group

For any Q-action ρ:Q→Perm(E), the F₂-chain module C₁=E→ZMod2
has its genuine inverse-indexed left action, already certified in
DLFChainPermutationAction. We assemble it into a strict group
whose elements are pairs (g,c), with multiplication
  (g,c)*(h,d)=(gh,c+g·d)
and inverse
  (g,c)⁻¹=(g⁻¹, -(g⁻¹·c)).

All equations are proved from the exact noncommutative group
action law, distributivity over addition, and the additive group
laws on coefficient functions. No action on a graph, order-two
hypotheses, finite-cover boundary constraint, or DLF theorem
is asserted here.

This fixes the multiplication order of the eventual relative
involution-killing extension and provides its canonical projection
to Q as an actual group homomorphism.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v
variable {Q : Type u} [Group Q] {E : Type v}

/-- Semidirect carrier of a group Q and its F₂ edge coefficient
module, using the specified literal permutation action. -/
@[ext] structure ChainSemidirect (rho : Q →* Equiv.Perm E) where
  base : Q
  chain : E → ZMod 2

instance (rho : Q →* Equiv.Perm E) : Mul (ChainSemidirect rho) where
  mul x y :=
    ⟨x.base * y.base,
      x.chain + chainPermutationAction rho x.base y.chain⟩

instance (rho : Q →* Equiv.Perm E) : One (ChainSemidirect rho) where
  one := ⟨1, 0⟩

instance (rho : Q →* Equiv.Perm E) : Inv (ChainSemidirect rho) where
  inv x :=
    ⟨x.base⁻¹, -(chainPermutationAction rho x.base⁻¹ x.chain)⟩

@[simp] theorem chainSemidirect_mul_base
    (rho : Q →* Equiv.Perm E) (x y : ChainSemidirect rho) :
    (x * y).base = x.base * y.base := rfl

@[simp] theorem chainSemidirect_mul_chain
    (rho : Q →* Equiv.Perm E) (x y : ChainSemidirect rho) :
    (x * y).chain =
      x.chain + chainPermutationAction rho x.base y.chain := rfl

@[simp] theorem chainSemidirect_one_base
    (rho : Q →* Equiv.Perm E) :
    (1 : ChainSemidirect rho).base = 1 := rfl

@[simp] theorem chainSemidirect_one_chain
    (rho : Q →* Equiv.Perm E) :
    (1 : ChainSemidirect rho).chain = 0 := rfl

@[simp] theorem chainSemidirect_inv_base
    (rho : Q →* Equiv.Perm E) (x : ChainSemidirect rho) :
    x⁻¹.base = x.base⁻¹ := rfl

@[simp] theorem chainSemidirect_inv_chain
    (rho : Q →* Equiv.Perm E) (x : ChainSemidirect rho) :
    x⁻¹.chain =
      -(chainPermutationAction rho x.base⁻¹ x.chain) := rfl

/-- The full noncommutative group law on actual chain semidirect
pairs; no quotient or unstated group extension involved. -/
instance (rho : Q →* Equiv.Perm E) : Group (ChainSemidirect rho) where
  mul_assoc a b c := by
    apply ChainSemidirect.ext
    · simp only [chainSemidirect_mul_base, mul_assoc]
    · change
        (a.chain + chainPermutationAction rho a.base b.chain) +
          chainPermutationAction rho (a.base * b.base) c.chain =
        a.chain + chainPermutationAction rho a.base
          (b.chain + chainPermutationAction rho b.base c.chain)
      rw [chainPermutationAction_mul, chainPermutationAction_add]
      abel
  one_mul a := by
    apply ChainSemidirect.ext
    · simp
    · change 0 + chainPermutationAction rho 1 a.chain = a.chain
      simp
  mul_one a := by
    apply ChainSemidirect.ext
    · simp
    · change a.chain + chainPermutationAction rho a.base 0 = a.chain
      simp
  inv_mul_cancel a := by
    apply ChainSemidirect.ext
    · simp
    · change
        -(chainPermutationAction rho a.base⁻¹ a.chain) +
          chainPermutationAction rho a.base⁻¹ a.chain = 0
      exact neg_add_cancel _

/-- The projection of the actual semidirect group onto Q is
a strict group homomorphism, with no normality assumptions. -/
def chainSemidirectBaseHom (rho : Q →* Equiv.Perm E) :
    ChainSemidirect rho →* Q where
  toFun := ChainSemidirect.base
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem chainSemidirectBaseHom_apply
    (rho : Q →* Equiv.Perm E) (x : ChainSemidirect rho) :
    chainSemidirectBaseHom rho x = x.base := rfl

/-- Every g∈Q is the image of the evident zero-chain element;
this is a surjection of underlying groups, not yet a section
of the prescribed boundary-constrained relative subgroup. -/
theorem chainSemidirectBaseHom_surjective
    (rho : Q →* Equiv.Perm E) :
    Function.Surjective (chainSemidirectBaseHom rho) := by
  intro g
  exact ⟨⟨g, 0⟩, rfl⟩

end RelativeDLF
end SemigenericEPPA
