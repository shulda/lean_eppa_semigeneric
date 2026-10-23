import SemigenericEPPA.Algebra.DLFChainSemidirectGroup
import Mathlib.Data.Finite.Defs

/-!
# Finiteness of the actual finite-chain semidirect group

The relative DLF cover uses a group whose underlying set is
Q × (E→ZMod2). Even when Q is nonabelian, the original
chain-semidirct product is canonically equivalent *as a type*
to this finite product. Its group law need not be commutative;
the underlying finite carrier does not depend on the action.

We supply a literal equivalence and obtain Finite for the
semidirect group and ALL of its subgroups, in particular for
the prescribed boundary-constrained subgroup constructed later.
No choice of enumeration, graph quotient or assumptions about
normality of H are needed.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v
variable {Q : Type u} [Group Q] {E : Type v}

/-- The semidirect group is type-equivalent to the raw pair of
the group component and F₂ chain component. -/
def chainSemidirectEquivProd
    (rho : Q →* Equiv.Perm E) :
    ChainSemidirect rho ≃ Q × (E → ZMod 2) where
  toFun a := (a.base, a.chain)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by
    intro a
    cases a
    rfl
  right_inv := by
    intro p
    rfl

/-- The genuine finite-chain semidirect product has finite carrier
for every finite Q and finite edge set E. -/
instance finite_chainSemidirect
    (rho : Q →* Equiv.Perm E) [Finite Q] [Finite E] :
    Finite (ChainSemidirect rho) := by
  classical
  exact Finite.of_equiv (Q × (E → ZMod 2))
    (chainSemidirectEquivProd rho).symm

/-- The boundary-constrained cover is a subgroup of an
automatically finite group; no need for a cardinality formula
or a special graph action in this argument. -/
theorem finite_chainSemidirect_subgroup
    (rho : Q →* Equiv.Perm E) [Finite Q] [Finite E]
    (K : Subgroup (ChainSemidirect rho)) :
    Finite K := by
  infer_instance

end RelativeDLF
end SemigenericEPPA
