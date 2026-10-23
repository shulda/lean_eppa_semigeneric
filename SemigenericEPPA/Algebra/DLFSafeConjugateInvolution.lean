import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport
import SemigenericEPPA.Structure.EffectiveGeometry
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Coset.Defs

/-!
# Good-orbit safety of involutions is invariant under group conjugacy

A relative finite group cover kills all upstairs involutions whose
base projections are not conjugate into the prescribed finite
safe group H≤Q. To finish the finite safe-pair argument one
must also transfer safety from an H-involution to every
conjugate t=q*h*q⁻¹ in Q.

This is an elementary but indispensable geometric lemma:
conjugation transports the swapped effective pair through the
actual Q-action, while F is preserved EXACTLY by Q. Therefore
the entire good affine congruence orbit property of its colour
is preserved; no global good-set saturation is used.

The proof works for nonabelian Q, arbitrary effective group G,
and any affine anti-involution s. No finite group cover or
Fraïssé-limit assumptions are needed in this module.
-/

namespace SemigenericEPPA

universe u v w z
variable {Q : Type u} [Group Q]
variable {G : Type v} [Group G] {C : Type w}
variable {V : Type z}

/-- If every H-involution exchanging an effective cross-pair
has its entire colour congruence orbit good, the same holds
for every conjugate of such an involution in a larger
colour-preserving Q-action.

This is precisely the safety-transfer step used after the
relative finite cover has eliminated nonconjugate involutions. -/
theorem RawDatum.goodCompleteOrbitAt_conjugate_involution
    (d : RawDatum G C)
    (D : EffectiveGeometry d.s V)
    (rho : Q →* Equiv.Perm V)
    (hPart : ∀ (q : Q) (x y : V),
      D.part (rho q x) (rho q y) ↔ D.part x y)
    (hColour : ∀ (q : Q) (x y : V),
      ¬D.part x y →
      D.F (rho q x) (rho q y) = D.F x y)
    (H : Subgroup Q)
    (hSafe : ∀ (h : H), h * h = 1 →
      ∀ (x y : V), ¬D.part x y →
        rho h.val x = y → rho h.val y = x →
          d.GoodCompleteOrbitAt (D.F x y))
    (t q : Q) (h : H)
    (htwo : t * t = 1)
    (ht : t = q * h.val * q⁻¹)
    (x y : V) (hxy : ¬D.part x y)
    (hswapXY : rho t x = y)
    (hswapYX : rho t y = x) :
    d.GoodCompleteOrbitAt (D.F x y) := by
  have hconj : q * (h.val * h.val) * q⁻¹ = 1 := by
    calc
      q * (h.val * h.val) * q⁻¹ =
        (q * h.val * q⁻¹) * (q * h.val * q⁻¹) := by group
      _ = t * t := by rw [ht]
      _ = 1 := htwo
  have hsquare_val : h.val * h.val = 1 := by
    calc
      h.val * h.val =
        q⁻¹ * (q * (h.val * h.val) * q⁻¹) * q := by group
      _ = q⁻¹ * 1 * q := by rw [hconj]
      _ = 1 := by group
  have hsquare : h * h = 1 := Subtype.ext hsquare_val
  have hshift : h.val * q⁻¹ = q⁻¹ * t := by
    rw [ht]
    group
  have hswapTransfer (a b : V) (hab : rho t a = b) :
      rho h.val (rho q⁻¹ a) = rho q⁻¹ b := by
    calc
      rho h.val (rho q⁻¹ a) =
        rho (h.val * q⁻¹) a := by rw [map_mul]; rfl
      _ = rho (q⁻¹ * t) a := by rw [hshift]
      _ = rho q⁻¹ (rho t a) := by rw [map_mul]; rfl
      _ = rho q⁻¹ b := congrArg (rho q⁻¹) hab
  have hxyBack : ¬D.part (rho q⁻¹ x) (rho q⁻¹ y) := by
    intro hab
    exact hxy ((hPart q⁻¹ x y).mp hab)
  have hgood := hSafe h hsquare
    (rho q⁻¹ x) (rho q⁻¹ y) hxyBack
    (hswapTransfer x y hswapXY)
    (hswapTransfer y x hswapYX)
  have hcol : D.F (rho q⁻¹ x) (rho q⁻¹ y) = D.F x y :=
    hColour q⁻¹ x y hxy
  simpa only [hcol] using hgood

end SemigenericEPPA
