import SemigenericEPPA.Algebra.RelativeDLFNoBadInvolutionParity
import SemigenericEPPA.Algebra.RelativeDLFGraphConnected
import SemigenericEPPA.Algebra.DLFChainPermutationAction

/-!
# No bad involution lifts with prescribed orbit boundary in relative Q/H graph

Let Q be an arbitrary finite group and H≤Q any subgroup (NOT
assumed normal). In the explicit three-layer relative graph, a
nonidentity involution t outside every conjugate of H acts without
fixed vertices or edges. The edge endpoints are separately
equivariant, so no edge is inverted.

If c:E→F₂ is fixed by the natural induced action of t and has
boundary δ_(basepoint)+δ_(t·basepoint), then c violates the direct
free-involution parity obstruction. We instantiate that generic
lemma with the EXACT graph, strict vertex and edge action
homomorphisms, no additional quotient-graph construction.

This is the mathematical heart of eliminating unwanted
involutive lifts in the finite relative group extension. The
actual semidirect extension and its finite group axioms remain
to be formalized separately.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u
variable {Q : Type u} [Group Q]

/-- No invariant edge-chain with the prescribed two-point boundary
exists for an involution not conjugate into H. This assumes finite
enumerations/orders of the explicitly finite graph vertex/edge
sets, to be instantiated from finiteness of Q in the group-cover
theorem. -/
theorem relativeGraph_no_badInvolutionInvariantBoundary
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [LinearOrder (CoverVertex H)]
    [Fintype (CoverEdge H)] [LinearOrder (CoverEdge H)]
    (t : Q)
    (ht : t * t = 1)
    (hBad : ∀ q : Q, q⁻¹ * t * q ∉ H)
    (c : CoverEdge H → ZMod 2)
    (hChainInvariant :
      chainPermutationAction (edgeAction H) t c = c)
    (x : CoverVertex H)
    (hBoundary : edgeBoundary (edgeSource H) (edgeTarget H) c =
      pointVertexChain x +
        pointVertexChain (vertexAction H t x)) :
    False := by
  have htne : t ≠ 1 := by
    intro heq
    apply hBad 1
    simpa [heq] using (H.one_mem)
  have hVInv (v : CoverVertex H) :
      vertexAction H t (vertexAction H t v) = v := by
    calc
      vertexAction H t (vertexAction H t v) =
          vertexAction H (t * t) v := by rw [map_mul]; rfl
      _ = v := by rw [ht]; simp
  have hEInv (e : CoverEdge H) :
      edgeAction H t (edgeAction H t e) = e := by
    calc
      edgeAction H t (edgeAction H t e) =
          edgeAction H (t * t) e := by rw [map_mul]; rfl
      _ = e := by rw [ht]; simp
  have hVFree (v : CoverVertex H) :
      vertexAction H t v ≠ v :=
    vertexAction_free_of_no_conjugate H t hBad v
  have hEFree (e : CoverEdge H) :
      edgeAction H t e ≠ e :=
    edgeAction_free_of_ne_one H t htne e
  have hEsource (e : CoverEdge H) :
      edgeSource H (edgeAction H t e) =
        vertexAction H t (edgeSource H e) :=
    edgeSource_equivariant H t e
  have hEtarget (e : CoverEdge H) :
      edgeTarget H (edgeAction H t e) =
        vertexAction H t (edgeTarget H e) :=
    edgeTarget_equivariant H t e
  have hTinverse : t⁻¹ = t := by
    calc
      t⁻¹ = t⁻¹ * (t * t) := by rw [ht]; simp
      _ = t := by group
  have hCInvariant (e : CoverEdge H) :
      c (edgeAction H t e) = c e := by
    have h := congrArg
      (fun f : CoverEdge H → ZMod 2 => f e) hChainInvariant
    change c (edgeAction H t⁻¹ e) = c e at h
    rwa [hTinverse] at h
  exact no_invariant_edgeChain_with_orbitBoundary
    (edgeSource H) (edgeTarget H)
    (vertexAction H t) (edgeAction H t)
    hVInv hVFree hEInv hEFree
    hEsource hEtarget c hCInvariant x hBoundary

end RelativeDLF
end SemigenericEPPA
