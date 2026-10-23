import SemigenericEPPA.Algebra.DLFChainSemidirectGroup

/-!
# Order-two lifts force invariance of their F₂ chain

In the finite relative involution-killing cover, the projection of
a putative order-two lift (t,c) satisfies t²=1. More importantly,
the second coordinate of the square is c+t·c, so if (t,c)²=1
the chain c must be t-invariant in characteristic two.

This lemma is generic for ANY group Q and any actual action
Q→Perm(E), even when Q is nonabelian or E is infinite. It is
the exact bridge from the finite chain semidirect group to the
direct no-bad-involution parity theorem in the explicit graph.

It makes no boundary or subgroup assumptions: those are imposed
separately by the prescribed-orbit-boundary subgroup.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v
variable {Q : Type u} [Group Q] {E : Type v}

/-- The projection of an order-two element also has square one. -/
theorem chainSemidirect_square_base
    (rho : Q →* Equiv.Perm E)
    (a : ChainSemidirect rho)
    (hOrderTwo : a * a = 1) :
    a.base * a.base = 1 := by
  have h := congrArg ChainSemidirect.base hOrderTwo
  simpa only [chainSemidirect_mul_base,
    chainSemidirect_one_base] using h

/-- Characteristic-two cancellation: if (t,c) has square one in
the true chain semidirect group, then t·c=c. The element t need
not be nontrivial for this implication. -/
theorem chainSemidirect_square_chain_invariant
    (rho : Q →* Equiv.Perm E)
    (a : ChainSemidirect rho)
    (hOrderTwo : a * a = 1) :
    chainPermutationAction rho a.base a.chain = a.chain := by
  have hChain : a.chain +
      chainPermutationAction rho a.base a.chain =
        (0 : E → ZMod 2) := by
    have h := congrArg ChainSemidirect.chain hOrderTwo
    simpa only [chainSemidirect_mul_chain,
      chainSemidirect_one_chain] using h
  funext e
  have hAt : a.chain e +
      chainPermutationAction rho a.base a.chain e = 0 := by
    have h := congrArg (fun f : E → ZMod 2 => f e) hChain
    exact h
  have hTwo : (2 : ZMod 2) = 0 := by decide
  have hSelf : a.chain e + a.chain e = 0 := by
    calc
      a.chain e + a.chain e =
          (2 : ZMod 2) * a.chain e := by ring
      _ = 0 := by rw [hTwo]; simp
  exact add_left_cancel (hAt.trans hSelf.symm)

end RelativeDLF
end SemigenericEPPA
