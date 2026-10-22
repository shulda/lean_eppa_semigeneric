import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# The augmentation obstruction for finite unoriented F₂ edge chains

The relative involution-killing group cover uses an F₂ edge chain
space C₁ and vertex chain space C₀, with boundary ∂(edge)=source+target.
The key quotient-parity contradiction is that an edge-chain boundary
in any finite loop-free (multi)graph has EVEN total vertex coefficient,
whereas a singleton vertex chain has odd augmentation.

This file formalizes that elementary parity statement directly for
finite types, allowing parallel edges. The boundary is defined on
functions E→ZMod 2; no graph quotient choices or homology libraries
are needed. It works even with loops, which contribute twice and
hence cancel. The stronger no-involution-lift argument additionally
needs to show that invariant edge chains descend to the quotient
graph without inverted edges, which is a separate subsequent gate.
-/

namespace SemigenericEPPA

universe u v
namespace RelativeDLF

variable {V : Type u} {E : Type v}
variable [Fintype V] [Fintype E]

/-- Linear F₂ boundary of an arbitrary finite unoriented graph with
possible parallel edges; every edge contributes at both endpoints. -/
def edgeBoundary (source target : E → V)
    (c : E → ZMod 2) : V → ZMod 2 :=
  fun x => ∑ e : E,
    ((if x = source e then c e else 0) +
      (if x = target e then c e else 0))

/-- Augmentation of a vertex chain, i.e. total F₂ parity. -/
def chainAugmentation (b : V → ZMod 2) : ZMod 2 :=
  ∑ x : V, b x

/-- In characteristic two every element cancels with itself. -/
private theorem zmodTwo_add_self (x : ZMod 2) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc
    x + x = (2 : ZMod 2) * x := by ring
    _ = 0 := by rw [h2]; simp

/-- EVERY finite F₂ edge-chain boundary has total augmentation 0.
This is independent of connectedness, freeness, and orientation. -/
theorem augmentation_edgeBoundary_zero
    (source target : E → V) (c : E → ZMod 2) :
    chainAugmentation (edgeBoundary source target c) = 0 := by
  classical
  unfold chainAugmentation edgeBoundary
  calc
    (∑ x : V, ∑ e : E,
        ((if x = source e then c e else 0) +
          (if x = target e then c e else 0))) =
      ∑ e : E, ∑ x : V,
        ((if x = source e then c e else 0) +
          (if x = target e then c e else 0)) := by
        rw [Finset.sum_comm]
    _ = ∑ e : E, (c e + c e) := by
      apply Finset.sum_congr rfl
      intro e he
      simp [Finset.sum_add_distrib]
    _ = 0 := by
      simp only [zmodTwo_add_self, Finset.sum_const_zero]

/-- One vertex has odd total parity, including when V has one
element. -/
def pointVertexChain (x : V) : V → ZMod 2 :=
  fun v => if v = x then 1 else 0

@[simp] theorem augmentation_pointVertexChain
    (x : V) :
    chainAugmentation (pointVertexChain x) = 1 := by
  classical
  simp [chainAugmentation, pointVertexChain]

/-- No F₂ edge chain of a finite graph has boundary equal to a
singleton vertex. This is the precise odd-boundary contradiction
eventually applied to the quotient graph of a bad involution. -/
theorem no_edgeBoundary_singleton
    (source target : E → V) (c : E → ZMod 2) (x : V)
    (hBoundary : edgeBoundary source target c = pointVertexChain x) :
    False := by
  have hAug : chainAugmentation (edgeBoundary source target c) =
      chainAugmentation (pointVertexChain x) :=
    congrArg chainAugmentation hBoundary
  rw [augmentation_edgeBoundary_zero,
      augmentation_pointVertexChain] at hAug
  exact (show (0 : ZMod 2) ≠ 1 by decide) hAug

end RelativeDLF
end SemigenericEPPA
