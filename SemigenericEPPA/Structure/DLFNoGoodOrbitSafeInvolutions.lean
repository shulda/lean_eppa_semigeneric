import SemigenericEPPA.Structure.RawPresentationEffectiveBridge
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport
import Mathlib.Algebra.Group.End

/-!
# First negative-DLF consequence: safe involutions fix every E-class

If no complete affine congruence orbit of effective colours is good,
then no safe finite group action can have an involution swapping
vertices from different E-classes. In fact every involution must
send each point into its OWN E-class.

The argument is exact: for h²=1 the pair (x,hx) is reversed by h.
If it were an E-cross pair, the local safety hypothesis would
supply GoodCompleteOrbitAt(F(x,hx)), contradicting
¬HasCompleteGoodOrbit. No global saturation or recentering s(1)=1
is assumed.

This is only the FIRST negative step. The delta-profile forcing
and orbit-killer extension arguments are separately needed to
rule out involutions staying within their E-classes, and the
finite-group parity argument is needed to finish the converse.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {H : Type t} [Group H]
variable {d : RawDatum G C}

/-- If there is no complete good affine congruence orbit,
any locally safe involution in an actual raw R1--R3 action
preserves each E-class setwise. -/
theorem safeInvolution_samePart_of_noCompleteGoodOrbit
    (P : RawRectanglePresentation d V)
    (hNoOrbit : ¬ d.HasCompleteGoodOrbit)
    (rho : H →* Equiv.Perm V)
    (hSafe : ∀ (h : H), h * h = 1 →
      ∀ (x y : V), ¬P.part x y →
        rho h x = y → rho h y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x y))
    (h : H) (hTwo : h * h = 1) (x : V) :
    P.part x (rho h x) := by
  classical
  by_contra hCross
  have hSquare : rho h (rho h x) = x := by
    have hIdentity : (rho (h * h)) x = x := by
      rw [hTwo, map_one]
      rfl
    simpa only [map_mul, Equiv.Perm.mul_apply] using hIdentity
  have hGood : d.GoodCompleteOrbitAt
      (P.effectiveReduct.F x (rho h x)) :=
    hSafe h hTwo x (rho h x) hCross rfl hSquare
  exact hNoOrbit
    ((d.hasCompleteGoodOrbit_iff_exists_goodCompleteOrbitAt).2
      ⟨P.effectiveReduct.F x (rho h x), hGood⟩)

end SemigenericEPPA
