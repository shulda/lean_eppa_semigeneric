import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge

/-!
# Complete-good-orbit safety for actual original-language raw witnesses

A faithful or merely strict H-action on an original R1--R3 raw
rectangle has a canonical effective reduct. The final DLF induction
needs the involution safety condition on the actual raw witness,
not on an unrelated auxiliary effective geometry.

We isolate the exact transport interface. Suppose the raw group
action projects equivariantly to a good-orbit-safe effective action,
and the original raw structure's induced effective colour agrees
with the projected base effective colour on every crossed pair.
Then every involution swapping a crossed raw pair has a COMPLETE
good orbit in the actual raw effective reduct.

This is intentionally agnostic about raw covers, phase choices,
faithfulness and finiteness. Later applications can discharge both
projection equalities using the certified fixed raw-cover
construction, and faithfulness using the prescribed old H-action.
-/

namespace SemigenericEPPA

universe u v w t z q
variable {G : Type u} [Group G] {C : Type v}
variable {W : Type w} {V : Type t}
variable {H : Type z} [Group H]
variable {d : RawDatum G C}

/-- Equivariant projection plus exact preservation of the
cross-part effective colour transports involution safety from a
base geometry to the *actual raw* R1--R3 presentation. -/
theorem rawPresentation_involutionCompleteOrbitSafe_of_projection
    (P : RawRectanglePresentation d W)
    (D : EffectiveGeometry d.s V)
    (proj : W → V)
    (rho : H →* Equiv.Perm V)
    (lift : H →* Equiv.Perm W)
    (hProj : ∀ (h : H) (x : W),
      proj (lift h x) = rho h (proj x))
    (hPart : ∀ x y : W,
      P.part x y ↔ D.part (proj x) (proj y))
    (hColour : ∀ x y : W, ¬P.part x y →
      P.effectiveReduct.F x y = D.F (proj x) (proj y))
    (hSafe : ∀ (h : H), h * h = 1 →
      ∀ (x y : V), ¬D.part x y →
        rho h x = y → rho h y = x →
          d.GoodCompleteOrbitAt (D.F x y))
    (h : H) (htwo : h * h = 1)
    (X Y : W) (hcross : ¬P.part X Y)
    (hXY : lift h X = Y)
    (hYX : lift h Y = X) :
    d.GoodCompleteOrbitAt (P.effectiveReduct.F X Y) := by
  have hBaseCross : ¬D.part (proj X) (proj Y) := by
    intro hp
    exact hcross ((hPart X Y).mpr hp)
  rw [hColour X Y hcross]
  exact hSafe h htwo (proj X) (proj Y) hBaseCross
    ((hProj h X).symm.trans (congrArg proj hXY))
    ((hProj h Y).symm.trans (congrArg proj hYX))

end SemigenericEPPA
