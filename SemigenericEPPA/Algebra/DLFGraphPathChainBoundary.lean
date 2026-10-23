import SemigenericEPPA.Algebra.DLFBoundaryHomAndDeltaAction
import SemigenericEPPA.Algebra.RelativeDLFGraphConnected

/-!
# Graph paths have F₂ boundaries equal to their two endpoints

The finite relative DLF group cover requires surjectivity onto Q
for pairs (g,c) with ∂c=δ_x0+δ_(g·x0). This is purely
graph-theoretic: connectedness supplies an edge path between
the two vertices, whose characteristic-two edge chain has the
desired boundary.

We prove the literal boundary of a singleton edge is the sum
of its two endpoint delta chains, then induct on the already
certified undirected connectedness relation. At concatenation,
the intermediate delta appears twice and cancels in F₂.
No choice of quotient multigraph, normality of H, or
unverified graph-theory library interface is involved.

Thus the explicit three-layer relative graph yields a chain
for every g∈Q. The construction of the boundary-constrained
subgroup and its projection is a separate group-theoretic gate.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v
variable {V : Type u} {E : Type v}
variable [Fintype V] [Fintype E]

/-- Boundary of a singleton F₂ edge chain, including loops (in
which case its two delta terms cancel). -/
theorem edgeBoundary_pointEdge
    (source target : E → V) (e : E) :
    edgeBoundary source target (pointVertexChain e) =
      pointVertexChain (source e) +
        pointVertexChain (target e) := by
  classical
  funext x
  change
    (∑ e' : E,
      ((if x = source e' then
          (if e' = e then (1 : ZMod 2) else 0) else 0) +
        (if x = target e' then
          (if e' = e then (1 : ZMod 2) else 0) else 0))) =
    (if x = source e then (1 : ZMod 2) else 0) +
      (if x = target e then (1 : ZMod 2) else 0)
  calc
    (∑ e' : E,
      ((if x = source e' then
          (if e' = e then (1 : ZMod 2) else 0) else 0) +
        (if x = target e' then
          (if e' = e then (1 : ZMod 2) else 0) else 0))) =
      ∑ e' : E,
        if e' = e then
          ((if x = source e' then (1 : ZMod 2) else 0) +
           (if x = target e' then 1 else 0))
        else 0 := by
      apply Finset.sum_congr rfl
      intro e' _
      by_cases he : e' = e
      · simp [he]
      · simp [he]
    _ = _ := by simp

/-- An arbitrary finite path in the literal relative graph
determines an F₂ chain with exactly its two endpoints as
boundary. The edge chain need not be a simple path. -/
theorem edgeConnected_exists_twoPointBoundary
    {Q : Type u} [Group Q]
    (H : Subgroup Q)
    [Fintype (CoverVertex H)]
    [Fintype (CoverEdge H)]
    (x y : CoverVertex H)
    (h : EdgeConnected H x y) :
    ∃ c : CoverEdge H → ZMod 2,
      edgeBoundary (edgeSource H) (edgeTarget H) c =
        pointVertexChain x + pointVertexChain y := by
  induction h with
  | refl x =>
      refine ⟨0, ?_⟩
      rw [edgeBoundary_zero, pointVertexChain_add_self]
  | step hstep =>
      obtain ⟨e, h | h⟩ := hstep
      · refine ⟨pointVertexChain e, ?_⟩
        rw [edgeBoundary_pointEdge, h.1, h.2]
      · refine ⟨pointVertexChain e, ?_⟩
        rw [edgeBoundary_pointEdge, h.1, h.2]
        exact add_comm _ _
  | trans hxy hyz ihxy ihyz =>
      obtain ⟨c1, hc1⟩ := ihxy
      obtain ⟨c2, hc2⟩ := ihyz
      refine ⟨c1 + c2, ?_⟩
      rw [edgeBoundary_add, hc1, hc2]
      calc
        (pointVertexChain _ + pointVertexChain _) +
          (pointVertexChain _ + pointVertexChain _) =
          pointVertexChain _ +
            (pointVertexChain _ + pointVertexChain _) +
              pointVertexChain _ := by simp only [add_assoc]
        _ = _ := by
          rw [pointVertexChain_add_self]
          simp
  | symm h ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c, ?_⟩
      rw [hc]
      exact add_comm _ _

/-- Every translate of the distinguished coset-layer basepoint
is joined by a finite chain; the exact boundary equation
needed for surjectivity of the relative group cover. -/
theorem relativeGraph_exists_prescribedBoundary
    {Q : Type u} [Group Q]
    (H : Subgroup Q)
    [Fintype (CoverVertex H)]
    [Fintype (CoverEdge H)]
    (g : Q) :
    ∃ c : CoverEdge H → ZMod 2,
      edgeBoundary (edgeSource H) (edgeTarget H) c =
        pointVertexChain
          (Sum.inl (Quotient.mk (leftCosetSetoid H) (1 : Q))) +
        pointVertexChain
          (vertexAction H g
            (Sum.inl (Quotient.mk (leftCosetSetoid H) (1 : Q)))) :=
  edgeConnected_exists_twoPointBoundary H _ _
    (allVertices_edgeConnected H _ _)

end RelativeDLF
end SemigenericEPPA
