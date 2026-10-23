import SemigenericEPPA.Algebra.RelativeDLFEdgeBoundaryParity
import SemigenericEPPA.Algebra.DLFChainPermutationAction

/-!
# Linear F₂ graph boundary and the Q-equivariant vertex delta chains

The relative group extension needs the boundary ∂:C₁→C₀ as an actual
homomorphism of additive groups, not merely a function with an
augmentation property. For each finite graph we construct this
homomorphism, prove point chains cancel in characteristic two,
and show the delta chain δ_x transforms into δ_(g·x) under
the inverse-indexed action of any group Q.

The final semidirect boundary-constrained subgroup will additionally
need ∂(g·c)=g·∂c, proved using equivariance of endpoints in a
separate module. This file contains no unverified global action
claims and no DLF theorem.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v w
variable {V : Type u} {E : Type v}
variable [Fintype V] [Fintype E]

/-- Zero edge coefficients have zero vertex boundary. -/
@[simp] theorem edgeBoundary_zero
    (source target : E → V) :
    edgeBoundary source target (0 : E → ZMod 2) = 0 := by
  classical
  funext x
  simp [edgeBoundary]

/-- The finite edge boundary is literally additive in F₂
coefficients, with no orientation or no-loop hypotheses. -/
theorem edgeBoundary_add
    (source target : E → V)
    (c d : E → ZMod 2) :
    edgeBoundary source target (c + d) =
      edgeBoundary source target c +
        edgeBoundary source target d := by
  classical
  funext x
  change
    (∑ e : E,
      ((if x = source e then c e + d e else 0) +
        (if x = target e then c e + d e else 0))) =
      (∑ e : E,
        ((if x = source e then c e else 0) +
          (if x = target e then c e else 0))) +
      (∑ e : E,
        ((if x = source e then d e else 0) +
          (if x = target e then d e else 0)))
  calc
    (∑ e : E,
      ((if x = source e then c e + d e else 0) +
        (if x = target e then c e + d e else 0))) =
      ∑ e : E,
        (((if x = source e then c e else 0) +
          (if x = target e then c e else 0)) +
         ((if x = source e then d e else 0) +
          (if x = target e then d e else 0))) := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases hs : x = source e <;>
        by_cases ht : x = target e <;>
          simp [hs, ht] <;> abel
    _ = _ := by rw [Finset.sum_add_distrib]

/-- The actual group homomorphism ∂:C₁→C₀ of finite F₂ chains. -/
noncomputable def edgeBoundaryHom
    (source target : E → V) :
    (E → ZMod 2) →+ (V → ZMod 2) where
  toFun := edgeBoundary source target
  map_zero' := edgeBoundary_zero source target
  map_add' := edgeBoundary_add source target

@[simp] theorem edgeBoundaryHom_apply
    (source target : E → V) (c : E → ZMod 2) :
    edgeBoundaryHom source target c =
      edgeBoundary source target c := rfl

/-- Delta chains are 2-torsion, a crucial cancellation in the
relative-cover boundary equation. -/
theorem pointVertexChain_add_self (x : V) :
    pointVertexChain x + pointVertexChain x =
      (0 : V → ZMod 2) := by
  classical
  funext v
  change (if v = x then (1 : ZMod 2) else 0) +
    (if v = x then 1 else 0) = 0
  by_cases hv : v = x
  · simp [hv]
    decide
  · simp [hv]

/-- Permuting vertices pulls a delta chain along the inverse
permutation, exactly as required by the semidirect coefficient
action. No preferred graph orientation or selected representative. -/
theorem chainPermutationAction_pointVertexChain
    {Q : Type w} [Group Q]
    (rhoV : Q →* Equiv.Perm V)
    (g : Q) (x : V) :
    chainPermutationAction rhoV g (pointVertexChain x) =
      pointVertexChain (rhoV g x) := by
  classical
  funext v
  have hEq : rhoV g⁻¹ v = x ↔ v = rhoV g x := by
    constructor
    · intro h
      calc
        v = rhoV g (rhoV g⁻¹ v) := by
          rw [← map_mul, mul_inv_cancel, map_one]
          rfl
        _ = rhoV g x := congrArg (rhoV g) h
    · intro h
      rw [h]
      calc
        rhoV g⁻¹ (rhoV g x) =
          rhoV (g⁻¹ * g) x := by rw [map_mul]; rfl
        _ = x := by simp
  change (if rhoV g⁻¹ v = x then (1 : ZMod 2) else 0) =
    (if v = rhoV g x then 1 else 0)
  simp only [hEq]

end RelativeDLF
end SemigenericEPPA
