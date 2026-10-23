import SemigenericEPPA.Algebra.DLFPrescribedBoundarySubgroup
import SemigenericEPPA.Algebra.RelativeDLFGraphNoBadInvolution
import SemigenericEPPA.Algebra.DLFChainSemidirectInvolution

/-!
# The actual relative subgroup has no bad involutive lift

For any group Q and subgroup H, instantiate the boundary-constrained
semidirect subgroup with the EXACT three-layer graph of the finite
relative cover. Its elements (g,c) satisfy
  ∂c = δ_H + δ_(g·H)
where vertex and edge actions use the certified strict Q actions.

If an element (t,c) of THIS SUBGROUP squares to the identity and
t is not conjugate into H, then the semidirect square equation makes
c t-invariant. Meanwhile the subgroup membership equation gives its
prescribed two-point boundary. The already-certified direct finite
graph parity theorem gives a contradiction.

This is a structural no-bad-involution theorem of the ACTUAL relative
subgroup, not just an isolated chain obstruction. Neither the
projection's surjectivity nor a section of H is asserted here.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u
variable {Q : Type u} [Group Q]

/-- Basepoint given by the identity coset H in the first layer. -/
def relativeBaseVertex (H : Subgroup Q) : CoverVertex H :=
  Sum.inl (Quotient.mk (leftCosetSetoid H) (1 : Q))

/-- The ACTUAL subgroup cut out by the orbit boundary equation
in the explicit relative graph. -/
noncomputable def relativeBoundaryCover
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [Fintype (CoverEdge H)] :
    Subgroup (ChainSemidirect (edgeAction H)) :=
  prescribedOrbitBoundarySubgroup
    (edgeAction H) (vertexAction H)
    (edgeBoundaryHom (edgeSource H) (edgeTarget H))
    (edgeBoundaryHom_action_equivariant
      (vertexAction H) (edgeAction H)
      (edgeSource H) (edgeTarget H)
      (edgeSource_equivariant H) (edgeTarget_equivariant H))
    (relativeBaseVertex H)

/-- Any element of the boundary-constrained relative cover that
has square one cannot project to a bad t outside the union of all
conjugates of the prescribed subgroup H. -/
theorem relativeBoundaryCover_noBadInvolutiveLift
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [LinearOrder (CoverVertex H)]
    [Fintype (CoverEdge H)] [LinearOrder (CoverEdge H)]
    (a : relativeBoundaryCover H)
    (ha : a.val * a.val = 1)
    (hBad : ∀ q : Q, q⁻¹ * a.val.base * q ∉ H) :
    False := by
  have hTwo : a.val.base * a.val.base = 1 :=
    chainSemidirect_square_base (edgeAction H) a.val ha
  have hInvariant :
      chainPermutationAction (edgeAction H) a.val.base a.val.chain =
        a.val.chain :=
    chainSemidirect_square_chain_invariant (edgeAction H) a.val ha
  have hBoundary :
      edgeBoundary (edgeSource H) (edgeTarget H) a.val.chain =
        pointVertexChain (relativeBaseVertex H) +
          pointVertexChain (vertexAction H a.val.base
            (relativeBaseVertex H)) := by
    exact a.property
  exact relativeGraph_no_badInvolutionInvariantBoundary
    H a.val.base hTwo hBad a.val.chain hInvariant
    (relativeBaseVertex H) hBoundary

end RelativeDLF
end SemigenericEPPA
