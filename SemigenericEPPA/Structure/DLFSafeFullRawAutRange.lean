import SemigenericEPPA.Structure.RawPresentationEffectiveBridge
import Mathlib.Algebra.Group.Subgroup.Ker
import SemigenericEPPA.Structure.DLFFullRawAutomorphismGroup
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport

/-!
# A faithful safe finite H embeds as a safe subgroup of full raw Aut(P)

For the DLF relative group cover we take Q to be the actual
finite original-language automorphism group of an EPPA witness.
An already certified faithful safe H-action defines an injective
homomorphism into Q; its range is a subgroup isomorphic to H.

Every involution of this image subgroup comes from an actual
H-involution (injectivity is essential for the square-one claim).
Its swapped cross-E pairs have precisely the same complete-good
congruence orbit as in the original H action.

This is the missing local safety input for applying the finite
split involution-killing cover to Q = Aut_raw(P).
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- The image of a faithful, complete-good-orbit-safe raw H-action
inside the literal full original-language automorphism group
is safe for every subgroup involution. -/
theorem fullRawAutHom_range_involutionSafe
    (P : RawRectanglePresentation d V)
    (rho : H →* Equiv.Perm V)
    (hPart : ∀ (h : H) (x y : V),
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hColour : ∀ (h : H) (x y : V),
      P.colour (rho h x) (rho h y) = P.colour x y)
    (hFaithful : Function.Injective rho)
    (hSafe : ∀ (h : H), h * h = 1 →
      ∀ (x y : V), ¬P.part x y →
        rho h x = y → rho h y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x y))
    (k : (P.fullRawAutHom rho hPart hColour).range)
    (hk : k * k = 1)
    (x y : V) (hxy : ¬P.part x y)
    (hkx : P.fullRawAutAction k.val x = y)
    (hky : P.fullRawAutAction k.val y = x) :
    d.GoodCompleteOrbitAt (P.effectiveReduct.F x y) := by
  classical
  let f : H →* P.fullRawAutGroup :=
    P.fullRawAutHom rho hPart hColour
  obtain ⟨h, hh⟩ : ∃ h : H, f h = k.val := k.property
  have hinj : Function.Injective f :=
    P.fullRawAutHom_injective rho hPart hColour hFaithful
  have htwo : h * h = 1 := by
    apply hinj
    calc
      f (h * h) = f h * f h := map_mul f h h
      _ = k.val * k.val := by rw [hh]
      _ = 1 := congrArg Subtype.val hk
      _ = f 1 := (map_one f).symm
  have hAction : P.fullRawAutAction k.val = rho h := by
    change (k.val.val : Equiv.Perm V) = rho h
    exact (congrArg Subtype.val hh).symm
  have hx : rho h x = y := by
    rw [← hAction]
    exact hkx
  have hy : rho h y = x := by
    rw [← hAction]
    exact hky
  exact hSafe h htwo x y hxy hx hy

end RawRectanglePresentation
end SemigenericEPPA
