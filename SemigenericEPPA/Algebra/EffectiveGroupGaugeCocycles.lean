import SemigenericEPPA.Structure.EffectiveGeometry
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Group

/-!
# Gauge cocycles for genuine finite-group actions

The positive coherent-EPPA construction (§4) associates to an
effective H-action on old real labels and part indices both
multipliers M^h_{ij} and correction twists L^h_{x,j}.

The crucial group-law requirements are (4.26) and (4.27):
  M^{kh}_{ij} = M^k_{h i,h j} M^h_{ij},
  L^{kh}_{x,j} = L^k_{h x,h j} L^h_{x,j}.

These are literal noncommutative equations. We isolate their
algebra independently of the finite valuation witness and of
the later cross-colour safety argument.

First, the reference-ratio choice
  L^h_{x,j} = z_{h x,h j}^{-1} z_{x,j}
satisfies the group cocycle equation automatically.

Second, whenever gauge multipliers realize the action on the
actual coordinate matrix a(x,j), their cocycle equation follows
on every occupied source part by right cancellation, without
extra commutativity or distinguished representatives.
-/

namespace SemigenericEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {V : Type w} {I : Type t}

/-- Reference-gauge ratios for an H-action on vertices and parts. -/
def referenceGaugeTwist
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (z : V → I → G)
    (h : H) (x : V) (j : I) : G :=
  (z (rho h x) (iota h j))⁻¹ * z x j

/-- The reference gauge is a literal (noncommutative) cocycle,
with the multiplication order in manuscript (4.27). -/
theorem referenceGaugeTwist_mul
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (z : V → I → G)
    (k h : H) (x : V) (j : I) :
    referenceGaugeTwist rho iota z (k * h) x j =
      referenceGaugeTwist rho iota z k (rho h x) (iota h j) *
        referenceGaugeTwist rho iota z h x j := by
  have hx : rho (k * h) x = rho k (rho h x) := by
    rw [map_mul]
    rfl
  have hj : iota (k * h) j = iota k (iota h j) := by
    rw [map_mul]
    rfl
  unfold referenceGaugeTwist
  rw [hx, hj]
  group

@[simp] theorem referenceGaugeTwist_one
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (z : V → I → G)
    (x : V) (j : I) :
    referenceGaugeTwist rho iota z 1 x j = 1 := by
  simp [referenceGaugeTwist]

/-- If a group action is represented by gauge multipliers on every
old vertex, the multipliers satisfy (4.26) on each OCCUPIED source
part. This is exactly the hypothesis used before adding neutral
defaults on unoccupied parts. -/
theorem occupiedGaugeMultiplier_cocycle
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (cls : V → I)
    (a : V → I → G)
    (m : H → I → I → G)
    (hcls : ∀ h : H, ∀ x : V,
      cls (rho h x) = iota h (cls x))
    (hm : ∀ h : H, ∀ x : V, ∀ j : I,
      a (rho h x) (iota h j) =
        m h (cls x) j * a x j)
    (k h : H) (i j : I) (hi : ∃ x : V, cls x = i) :
    m (k * h) i j =
      m k (iota h i) (iota h j) * m h i j := by
  obtain ⟨x, hx⟩ := hi
  have hclass : cls (rho h x) = iota h i := by
    rw [hcls h x, hx]
  have hmulx : rho (k * h) x = rho k (rho h x) := by
    rw [map_mul]
    rfl
  have hmuli : iota (k * h) j = iota k (iota h j) := by
    rw [map_mul]
    rfl
  have hcancel :
      m (k * h) i j * a x j =
        (m k (iota h i) (iota h j) * m h i j) * a x j := by
    calc
      m (k * h) i j * a x j =
        a (rho (k * h) x) (iota (k * h) j) := by
          simpa only [hx] using (hm (k * h) x j).symm
      _ = a (rho k (rho h x)) (iota k (iota h j)) := by
            rw [hmulx, hmuli]
      _ = m k (cls (rho h x)) (iota h j) *
          a (rho h x) (iota h j) := hm k (rho h x) (iota h j)
      _ = (m k (iota h i) (iota h j) * m h i j) *
            a x j := by
            rw [hclass, hm h x j, hx]
            group
  exact mul_right_cancel hcancel

end SemigenericEPPA
