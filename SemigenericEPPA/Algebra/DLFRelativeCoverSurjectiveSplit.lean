import SemigenericEPPA.Algebra.DLFActualRelativeCoverNoBadInvolution
import SemigenericEPPA.Algebra.DLFGraphPathChainBoundary

/-!
# Surjective relative group cover with a split copy of H

The actual boundary-constrained subgroup of Q⋉(E→F₂) admits a
surjective group homomorphism to Q: the three-layer graph is
connected, so every δ_H + δ_(g·H) is the boundary of a finite
edge chain.

The original subgroup H embeds homomorphically by h↦(h,0).
Its elements fix the distinguished identity coset H∈Q/H,
and hence the zero edge-chain has exactly the prescribed
boundary. Both statements use the SAME fixed boundary subgroup,
the SAME graph and the SAME action used for the no-bad-involution
theorem. H is not assumed normal in Q.

Together with the earlier no-bad-involution theorem, this
constructs the central algebraic exact-cover API. Finiteness
and the subsequent realization as actual R1–R3 automorphisms
are handled separately.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u
variable {Q : Type u} [Group Q]

/-- Genuine group projection from the boundary-constrained cover
onto its prescribed ambient finite group Q. -/
noncomputable def relativeCoverProjection
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [Fintype (CoverEdge H)] :
    relativeBoundaryCover H →* Q :=
  (chainSemidirectBaseHom (edgeAction H)).comp
    (relativeBoundaryCover H).subtype

@[simp] theorem relativeCoverProjection_apply
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [Fintype (CoverEdge H)]
    (a : relativeBoundaryCover H) :
    relativeCoverProjection H a = a.val.base := rfl

/-- Surjectivity uses exactly the graph-connectedness
two-point boundary chain lemma and nothing stronger. -/
theorem relativeCoverProjection_surjective
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [Fintype (CoverEdge H)] :
    Function.Surjective (relativeCoverProjection H) := by
  intro g
  obtain ⟨c, hc⟩ := relativeGraph_exists_prescribedBoundary H g
  refine ⟨⟨⟨g, c⟩, ?_⟩, rfl⟩
  exact hc

/-- Every original element h∈H fixes the identity coset
as a vertex of the relative graph, with no normality assumption. -/
theorem relativeBaseVertex_fixed_by_H
    (H : Subgroup Q) (h : H) :
    vertexAction H h.val (relativeBaseVertex H) =
      relativeBaseVertex H := by
  have hfix : leftCosetAction H h.val
      (Quotient.mk (leftCosetSetoid H) (1 : Q)) =
      Quotient.mk (leftCosetSetoid H) (1 : Q) := by
    apply (leftCosetAction_fixed_iff H h.val 1).mpr
    simpa using h.property
  simpa only [relativeBaseVertex, vertexPerm_coset] using
    congrArg Sum.inl hfix

/-- The zero-chain lift h↦(h,0) is a strict homomorphism
from H into the exact boundary-constrained group cover. -/
noncomputable def relativeCoverSection
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [Fintype (CoverEdge H)] :
    H →* relativeBoundaryCover H where
  toFun h := ⟨⟨h.val, 0⟩, by
    change
      edgeBoundary (edgeSource H) (edgeTarget H)
          (0 : CoverEdge H → ZMod 2) =
        pointVertexChain (relativeBaseVertex H) +
          pointVertexChain
            (vertexAction H h.val (relativeBaseVertex H))
    rw [edgeBoundary_zero, relativeBaseVertex_fixed_by_H H h]
    exact (pointVertexChain_add_self (relativeBaseVertex H)).symm⟩
  map_one' := by
    apply Subtype.ext
    apply ChainSemidirect.ext
    · rfl
    · rfl
  map_mul' := by
    intro h k
    apply Subtype.ext
    apply ChainSemidirect.ext
    · rfl
    · change (0 : CoverEdge H → ZMod 2) =
        0 + chainPermutationAction (edgeAction H) h.val 0
      simp

/-- This homomorphic section projects to the original element
of H, exactly, not merely up to conjugacy or quotient classes. -/
theorem relativeCoverProjection_section
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [Fintype (CoverEdge H)]
    (h : H) :
    relativeCoverProjection H (relativeCoverSection H h) = h.val := rfl

/-- The relative cover contains a faithful copy of H. -/
theorem relativeCoverSection_injective
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [Fintype (CoverEdge H)] :
    Function.Injective (relativeCoverSection H) := by
  intro h k heq
  apply Subtype.ext
  exact (relativeCoverProjection_section H h).symm.trans
    ((congrArg (relativeCoverProjection H) heq).trans
      (relativeCoverProjection_section H k))

end RelativeDLF
end SemigenericEPPA
