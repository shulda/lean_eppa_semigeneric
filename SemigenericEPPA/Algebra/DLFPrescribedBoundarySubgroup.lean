import SemigenericEPPA.Algebra.DLFBoundaryEquivariant
import SemigenericEPPA.Algebra.DLFChainSemidirectGroup

/-!
# Boundary-constrained relative F₂ semidirect group

For Q acting on E and V by strict permutations, and for an
additive boundary ∂:F₂^E→F₂^V commuting with these actions,
the audited relative cover consists of pairs (g,c) satisfying

   ∂c = δ_x0 + δ_(g·x0).

We package these elements as an ACTUAL subgroup of the chain
semidirect group Q⋉F₂^E (the latter is defined separately).
Closure under multiplication is the telescoping identity

 (δ_x0+δ_gx0) + g·(δ_x0+δ_hx0)
     = δ_x0 + δ_(ghx0),

where every point chain has order at most two. Inversion is the
same identity transported through g⁻¹. No commutativity of Q,
normality of H or origin recentering is assumed.

Here boundary equivariance is a parameter so this lemma is
reusable for other finite graphs. The certified graph-boundary
naturality lemma discharges it for the explicit relative-cover
graph in the next instantiation. No surjectivity, splitting,
or no-bad-involution claim is made yet.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v w
variable {Q : Type u} [Group Q] {V : Type v} {E : Type w}
variable [Fintype V]

/-- In characteristic two, the additive inverse of any
F₂-valued vertex chain equals the chain itself. -/
theorem neg_eq_self_F2_chain (u : V → ZMod 2) : -u = u := by
  funext x
  change -(u x) = u x
  have hnegOne : (-1 : ZMod 2) = 1 := by decide
  calc
    -(u x) = (-1 : ZMod 2) * u x := by ring
    _ = u x := by rw [hnegOne]; simp

/-- Genuine finite relative-cover subgroup cut out by the
cocycle boundary equation, in the true noncommutative
semidirect group. -/
def prescribedOrbitBoundarySubgroup
    (rhoE : Q →* Equiv.Perm E)
    (rhoV : Q →* Equiv.Perm V)
    (boundary : (E → ZMod 2) →+ (V → ZMod 2))
    (hBoundaryEquiv : ∀ (g : Q) (c : E → ZMod 2),
      boundary (chainPermutationAction rhoE g c) =
        chainPermutationAction rhoV g (boundary c))
    (x0 : V) :
    Subgroup (ChainSemidirect rhoE) where
  carrier := {a |
    boundary a.chain =
      pointVertexChain x0 + pointVertexChain (rhoV a.base x0)}
  one_mem' := by
    change boundary (0 : E → ZMod 2) =
      pointVertexChain x0 + pointVertexChain (rhoV 1 x0)
    simpa only [map_zero, map_one, Equiv.Perm.one_apply,
      pointVertexChain_add_self]
  mul_mem' := by
    intro a b ha hb
    change
      boundary (a.chain +
        chainPermutationAction rhoE a.base b.chain) =
      pointVertexChain x0 +
        pointVertexChain (rhoV (a.base * b.base) x0)
    rw [map_add, hBoundaryEquiv, ha, hb,
      chainPermutationAction_add,
      chainPermutationAction_pointVertexChain,
      chainPermutationAction_pointVertexChain]
    have hcomp :
        rhoV a.base (rhoV b.base x0) =
          rhoV (a.base * b.base) x0 := by
      rw [map_mul]
      rfl
    rw [hcomp]
    calc
      (pointVertexChain x0 +
        pointVertexChain (rhoV a.base x0)) +
        (pointVertexChain (rhoV a.base x0) +
          pointVertexChain (rhoV (a.base * b.base) x0)) =
      pointVertexChain x0 +
        (pointVertexChain (rhoV a.base x0) +
          pointVertexChain (rhoV a.base x0)) +
        pointVertexChain (rhoV (a.base * b.base) x0) := by abel
      _ = pointVertexChain x0 +
          pointVertexChain (rhoV (a.base * b.base) x0) := by
        rw [pointVertexChain_add_self]
        simp
  inv_mem' := by
    intro a ha
    change boundary
        (-(chainPermutationAction rhoE a.base⁻¹ a.chain)) =
      pointVertexChain x0 +
        pointVertexChain (rhoV a.base⁻¹ x0)
    rw [map_neg, hBoundaryEquiv, ha,
      chainPermutationAction_add,
      chainPermutationAction_pointVertexChain,
      chainPermutationAction_pointVertexChain]
    have hInv :
        rhoV a.base⁻¹ (rhoV a.base x0) = x0 := by
      calc
        rhoV a.base⁻¹ (rhoV a.base x0) =
            rhoV (a.base⁻¹ * a.base) x0 := by rw [map_mul]; rfl
        _ = x0 := by simp
    rw [hInv, neg_eq_self_F2_chain]
    exact add_comm _ _

end RelativeDLF
end SemigenericEPPA
