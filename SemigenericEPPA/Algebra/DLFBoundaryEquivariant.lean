import SemigenericEPPA.Algebra.DLFBoundaryHomAndDeltaAction

/-!
# The actual F₂ graph boundary is equivariant for vertex and edge actions

Let a group Q act on the vertices and edges of a finite graph with
the source and target maps separately equivariant. The inverse-
indexed action on edge and vertex F₂-valued coefficients then
commutes EXACTLY with the edge-boundary homomorphism ∂.

This fact is the last compatibility needed before defining the
subgroup of (q,c) in Q⋉C₁ satisfying
  ∂c = δ_x0 + δ_(q·x0).

It does not assume Q abelian, equal edge and vertex actions,
no inverted edges, orbit transversals, or any particular graph.
It is not yet a group-cover or DLF theorem.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v w
variable {Q : Type u} [Group Q]
variable {V : Type v} {E : Type w}
variable [Fintype V] [Fintype E]

/-- Exact equivariance of the F₂ edge boundary with respect to
inverse-indexed genuine left group actions on both carriers. -/
theorem edgeBoundary_action_equivariant
    (rhoV : Q →* Equiv.Perm V)
    (rhoE : Q →* Equiv.Perm E)
    (source target : E → V)
    (hSource : ∀ (g : Q) (e : E),
      source (rhoE g e) = rhoV g (source e))
    (hTarget : ∀ (g : Q) (e : E),
      target (rhoE g e) = rhoV g (target e))
    (g : Q) (c : E → ZMod 2) :
    edgeBoundary source target
        (chainPermutationAction rhoE g c) =
      chainPermutationAction rhoV g
        (edgeBoundary source target c) := by
  classical
  funext x
  change
    (∑ e : E,
      ((if x = source e then c (rhoE g⁻¹ e) else 0) +
        (if x = target e then c (rhoE g⁻¹ e) else 0))) =
    ∑ e : E,
      ((if rhoV g⁻¹ x = source e then c e else 0) +
        (if rhoV g⁻¹ x = target e then c e else 0))
  let f : E → ZMod 2 := fun e =>
    ((if x = source e then c (rhoE g⁻¹ e) else 0) +
      (if x = target e then c (rhoE g⁻¹ e) else 0))
  have hLeft (v : V) : rhoV g (rhoV g⁻¹ v) = v := by
    calc
      rhoV g (rhoV g⁻¹ v) = rhoV (g * g⁻¹) v := by rw [map_mul]; rfl
      _ = v := by simp
  have hRight (v : V) : rhoV g⁻¹ (rhoV g v) = v := by
    calc
      rhoV g⁻¹ (rhoV g v) = rhoV (g⁻¹ * g) v := by rw [map_mul]; rfl
      _ = v := by simp
  have hTransport (v : V) :
      x = rhoV g v ↔ rhoV g⁻¹ x = v := by
    constructor
    · intro hx
      rw [hx]
      exact hRight v
    · intro hx
      calc
        x = rhoV g (rhoV g⁻¹ x) := (hLeft x).symm
        _ = rhoV g v := congrArg (rhoV g) hx
  have hRightE (e : E) : rhoE g⁻¹ (rhoE g e) = e := by
    calc
      rhoE g⁻¹ (rhoE g e) = rhoE (g⁻¹ * g) e := by rw [map_mul]; rfl
      _ = e := by simp
  calc
    (∑ e : E, f e) =
      (∑ e : E, f (rhoE g e)) :=
        (Equiv.sum_comp (rhoE g) f).symm
    _ = ∑ e : E,
        ((if rhoV g⁻¹ x = source e then c e else 0) +
          (if rhoV g⁻¹ x = target e then c e else 0)) := by
      apply Finset.sum_congr rfl
      intro e _
      dsimp [f]
      rw [hSource g e, hTarget g e, hRightE e]
      simp only [hTransport (source e), hTransport (target e)]

/-- The same naturality as a strict AddMonoidHom equation, suitable
for defining the boundary-constrained semidirect subgroup. -/
theorem edgeBoundaryHom_action_equivariant
    (rhoV : Q →* Equiv.Perm V)
    (rhoE : Q →* Equiv.Perm E)
    (source target : E → V)
    (hSource : ∀ (g : Q) (e : E),
      source (rhoE g e) = rhoV g (source e))
    (hTarget : ∀ (g : Q) (e : E),
      target (rhoE g e) = rhoV g (target e))
    (g : Q) (c : E → ZMod 2) :
    edgeBoundaryHom source target
        (chainPermutationAction rhoE g c) =
      chainPermutationAction rhoV g
        (edgeBoundaryHom source target c) :=
  edgeBoundary_action_equivariant rhoV rhoE
    source target hSource hTarget g c

end RelativeDLF
end SemigenericEPPA
