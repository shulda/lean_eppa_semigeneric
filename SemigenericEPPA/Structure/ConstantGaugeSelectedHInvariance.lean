import SemigenericEPPA.Structure.ConstantSkeletonGauge
import SemigenericEPPA.Valuations.ConstantSkeletonOldEmbedding
import Mathlib.Algebra.Group.End

/-!
# Induced H-invariance survives constant-skeleton recoding

The relative effective H-multiplier theorem requires H-invariance
of the gauge-defined cross-colour matrix on a selected old subset
S, not of the entire old carrier V.

The fixed factorial geometry B first comes with its actual
E/F relations. A selected auxiliary H-action can preserve those
relations on S while completely changing F elsewhere. Before
applying the selected multipliers, B is recoded as its canonical
constant-skeleton indexed gauge P. We verify that this recoding
retains EXACTLY the restricted H-invariance needed by the
multiplier theorem, without any global F-automorphism premise.

This is a small but load-bearing proof-interface bridge:
the selected H-action need not preserve the old canonical gauge
coordinates, nor an auxiliary linear order, nor colours involving
vertices outside S. Only the actual effective E/F data on S
are used.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {V : Type v}
variable {H : Type w} [Group H]
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- H-automorphisms on ONLY a selected induced subset remain
H-automorphisms of the restricted effective matrix after a
constant-skeleton quotient gauge recoding. No F-invariance on
the complement of S is needed or implied. -/
theorem constantQuotientIndexedGauge_invariant_onSelected
    (D : EffectiveGeometry s V)
    [LinearOrder (Quotient D.part)]
    (g0 : G) (hfixed : s g0 = g0)
    (S : Set V)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ (h : H) (x y : S),
      D.part (rho h x.val) (rho h y.val) ↔
        D.part x.val y.val)
    (hF : ∀ (h : H) (x y : S),
      ¬D.part x.val y.val →
        D.F (rho h x.val) (rho h y.val) = D.F x.val y.val)
    (h : H) (x y : S)
    (hxy :
      (D.constantQuotientIndexedGauge g0 hfixed).label x.val ≠
      (D.constantQuotientIndexedGauge g0 hfixed).label y.val) :
    (D.constantQuotientIndexedGauge g0 hfixed).toEffectiveGeometry.F
      (rho h x.val) (rho h y.val) =
      (D.constantQuotientIndexedGauge g0 hfixed).toEffectiveGeometry.F
        x.val y.val := by
  have hOldCross : ¬D.part x.val y.val := by
    intro hab
    apply hxy
    change Quotient.mk D.part x.val = Quotient.mk D.part y.val
    exact Quotient.sound hab
  have hNewCross : ¬D.part (rho h x.val) (rho h y.val) := by
    intro hab
    exact hOldCross ((hE h x y).mp hab)
  calc
    (D.constantQuotientIndexedGauge g0 hfixed).toEffectiveGeometry.F
        (rho h x.val) (rho h y.val) =
      D.F (rho h x.val) (rho h y.val) :=
        D.constantQuotientIndexedGauge_cross
          g0 hfixed (rho h x.val) (rho h y.val) hNewCross
    _ = D.F x.val y.val := hF h x y hOldCross
    _ = (D.constantQuotientIndexedGauge g0 hfixed).toEffectiveGeometry.F
          x.val y.val :=
        (D.constantQuotientIndexedGauge_cross
          g0 hfixed x.val y.val hOldCross).symm

/-- Literal class-index compatibility is unchanged by constant
recoding: this is the original canonical quotient, not a new
abstract imaginary sort. -/
theorem constantQuotientIndexedGauge_class
    (D : EffectiveGeometry s V)
    [LinearOrder (Quotient D.part)]
    (g0 : G) (hfixed : s g0 = g0)
    (x : V) :
    (D.constantQuotientIndexedGauge g0 hfixed).label x =
      Quotient.mk D.part x := rfl

end EffectiveGeometry

end SemigenericEPPA
