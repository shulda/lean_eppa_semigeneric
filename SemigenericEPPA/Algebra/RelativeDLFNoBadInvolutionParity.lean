import SemigenericEPPA.Algebra.RelativeDLFEdgeBoundaryParity
import SemigenericEPPA.Algebra.DLFInvariantFreeInvolutionParity

/-!
# A direct relative DLF parity contradiction (NO quotient multigraph)

Fix a finite graph with arbitrary endpoints E → V and a free
involution on vertices and edges, respecting endpoints. Suppose a
ZMod 2 edge chain c is invariant under the edge involution, but its
boundary is the sum of a chosen vertex x and its distinct mate tx.

Choose one vertex from each t-orbit by a finite linear order and
write χ(v)=1 iff v<t(v). Then χ(tv)=1+χ(v). Weighted boundary
evaluation is ∑_e c(e)*(χ(source e)+χ(target e)).
This edge coefficient is invariant under t: both χ values flip,
and 1+1=0 in characteristic two. Since t freely permutes edges,
the total sum is zero by the certified invariant-sum parity lemma.
On the other hand the alleged boundary has weighted sum
χ(x)+χ(tx)=1. Contradiction.

No quotient multigraph and no descent of quotient edge chains are
needed. The theorem works for arbitrary finite multigraphs,
provided the involution has no inverted edges (source and target
are separately equivariant), as guaranteed by the certified
three-layer relative-cover graph construction.

It is a FINITE PARITY obstruction only. The semidirect group cover
and the DLF group construction are separate subsequent theorems.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v
variable {V : Type u} {E : Type v}
variable [Fintype V] [Fintype E]

/-- F₂ analogue of integration by parts for a finite graph: a
vertex potential evaluated on the edge boundary equals its
edgewise discrete gradient weighted by the edge coefficients. -/
theorem weighted_edgeBoundary
    (source target : E → V)
    (c : E → ZMod 2) (χ : V → ZMod 2) :
    (∑ x : V, χ x * edgeBoundary source target c x) =
      ∑ e : E, c e * (χ (source e) + χ (target e)) := by
  classical
  change
    (∑ x : V, χ x * ∑ e : E,
      ((if x = source e then c e else 0) +
        (if x = target e then c e else 0))) =
      ∑ e : E, c e * (χ (source e) + χ (target e))
  simp only [mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  calc
    (∑ x : V, χ x *
      ((if x = source e then c e else 0) +
        (if x = target e then c e else 0))) =
      (∑ x : V, χ x * (if x = source e then c e else 0)) +
        (∑ x : V, χ x *
          (if x = target e then c e else 0)) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = χ (source e) * c e + χ (target e) * c e := by
      simp [mul_ite]
    _ = c e * (χ (source e) + χ (target e)) := by ring

/-- A finite free vertex involution has a selector χ∈F₂ which
toggles on each pair of mate vertices. No choice of quotient
graph or ordering of the involution orbits is required. -/
theorem exists_toggle_selector
    [LinearOrder V]
    (tv : Equiv.Perm V)
    (hInvol : ∀ x : V, tv (tv x) = x)
    (hFree : ∀ x : V, tv x ≠ x) :
    ∃ χ : V → ZMod 2,
      ∀ x : V, χ (tv x) = 1 + χ x := by
  classical
  let χ : V → ZMod 2 :=
    fun x => if x < tv x then 1 else 0
  refine ⟨χ, ?_⟩
  intro x
  have hTwo : (1 : ZMod 2) + 1 = 0 := by decide
  change (if tv x < tv (tv x) then (1 : ZMod 2) else 0) =
    1 + (if x < tv x then 1 else 0)
  rw [hInvol x]
  by_cases hx : x < tv x
  · have hnot : ¬tv x < x := not_lt.mpr (le_of_lt hx)
    simp [hx, hnot, hTwo]
  · have ht : tv x < x :=
      lt_of_le_of_ne (le_of_not_gt hx) (hFree x)
    simp [hx, ht]

/-- A free edge involution cannot preserve an F₂ edge chain
whose boundary is the two-vertex orbit of a FREE vertex
involution. This is the parity obstruction in the relative
involution-killing cover, proved WITHOUT a quotient graph. -/
theorem no_invariant_edgeChain_with_orbitBoundary
    [LinearOrder V] [LinearOrder E]
    (source target : E → V)
    (tv : Equiv.Perm V)
    (te : Equiv.Perm E)
    (hVInvol : ∀ x : V, tv (tv x) = x)
    (hVFree : ∀ x : V, tv x ≠ x)
    (hEInvol : ∀ e : E, te (te e) = e)
    (hEFree : ∀ e : E, te e ≠ e)
    (hSource : ∀ e : E, source (te e) = tv (source e))
    (hTarget : ∀ e : E, target (te e) = tv (target e))
    (c : E → ZMod 2)
    (hInvariant : ∀ e : E, c (te e) = c e)
    (x : V)
    (hBoundary : edgeBoundary source target c =
      pointVertexChain x + pointVertexChain (tv x)) :
    False := by
  classical
  obtain ⟨χ, hToggle⟩ :=
    exists_toggle_selector tv hVInvol hVFree
  let f : E → ZMod 2 :=
    fun e => c e * (χ (source e) + χ (target e))
  have hFInvariant : ∀ e : E, f (te e) = f e := by
    intro e
    change c (te e) *
      (χ (source (te e)) + χ (target (te e))) =
      c e * (χ (source e) + χ (target e))
    rw [hInvariant e, hSource e, hTarget e,
        hToggle (source e), hToggle (target e)]
    have hTwo : (1 : ZMod 2) + 1 = 0 := by decide
    calc
      c e * ((1 + χ (source e)) + (1 + χ (target e))) =
        c e * ((1 + 1) + (χ (source e) + χ (target e))) := by ring
      _ = c e * (χ (source e) + χ (target e)) := by rw [hTwo, zero_add]
  have hZero : (∑ e : E, f e) = 0 :=
    sum_invariant_freeInvolution_zero te hEInvol hEFree f hFInvariant
  have hWeighted :
      (∑ v : V, χ v * edgeBoundary source target c v) =
        ∑ e : E, f e :=
    weighted_edgeBoundary source target c χ
  have hPoint :
      (∑ v : V, χ v *
        (pointVertexChain x v + pointVertexChain (tv x) v)) =
          χ x + χ (tv x) := by
    simp [pointVertexChain, mul_add, Finset.sum_add_distrib, mul_ite]
  have hOne : (∑ e : E, f e) = 1 := by
    rw [← hWeighted, hBoundary]
    change (∑ v : V, χ v *
      (pointVertexChain x v + pointVertexChain (tv x) v)) = 1
    rw [hPoint, hToggle x]
    have hTwo : (1 : ZMod 2) + 1 = 0 := by decide
    calc
      χ x + (1 + χ x) = 1 + (χ x + χ x) := by ring
      _ = 1 := by
        have hDup : χ x + χ x = 0 := by
          calc
            χ x + χ x = (1 + 1 : ZMod 2) * χ x := by ring
            _ = 0 := by rw [hTwo]; simp
        rw [hDup, add_zero]
  have hContr : (0 : ZMod 2) = 1 := hZero.symm.trans hOne
  exact (show (0 : ZMod 2) ≠ 1 by decide) hContr

end RelativeDLF
end SemigenericEPPA
