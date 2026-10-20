import SemigenericEPPA.Algebra.EffectiveGroupGaugeCocycles
import SemigenericEPPA.Algebra.Gauge
import Mathlib.Tactic.Group

/-!
# Construct the occupied pair multiplier from rank-one gauge invariance

In the full positive coherent-EPPA construction for arbitrary G,
the action of H on actual old vertices preserves the effective
rank-one matrix between two occupied old E-classes.

For old gauge rows aOld(x), transported rows aNew(x), and
corresponding column values bOld(y), bNew(y), the invariant
effective cross-colouring is

  s(aNew x) * bNew y = s(aOld x) * bOld y.

Fix ANY old reference row x0 and ANY old reference column y0.
The rectangle/rank-one equality implies

  aNew(x) * aOld(x)⁻¹ =
    aNew(x0) * aOld(x0)⁻¹

for EVERY x. Therefore ONE multiplier M, defined by the ratio
at x0, satisfies
  M * aOld(x) = aNew(x)
for ALL rows x, exactly as required in manuscript (4.24).

We prove this in the ORIGINAL affine anti-involution s, without
recentring at a reversal-fixed origin and WITHOUT assuming
commutativity or s(1)=1. It applies independently to any two
occupied E-classes and feeds the previously certified strict
noncommutative cocycle theorem
`occupiedGaugeMultiplier_cocycle`.

It does not construct the global H-action by itself.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G]
variable {X : Type v} {Y : Type w}

/-- Equality of normalized reverse-gauge ratios forces equality
of the original left row multipliers for any affine reversal. -/
theorem AffineAntiInvolution.rowRatio_eq_of_reverseRatio_eq
    (s : AffineAntiInvolution G)
    (aNew aOld bNew bOld : G)
    (hr : (s aNew)⁻¹ * s aOld = (s bNew)⁻¹ * s bOld) :
    aNew * aOld⁻¹ = bNew * bOld⁻¹ := by
  have hformula (new old : G) :
      s (new * old⁻¹) =
        s 1 * ((s new)⁻¹ * s old)⁻¹ := by
    rw [s.map_mul, s.reverse_inv_affine]
    group
  apply s.injective
  rw [hformula aNew aOld, hformula bNew bOld, hr]

/-- A rank-one matrix preserved by the old action has a
row gauge multiplier INDEPENDENT of the choice of reference
old row. Only one opposite reference column is needed. -/
theorem affineGauge_rowMultiplier_independent
    (s : AffineAntiInvolution G)
    (aOld aNew : X → G)
    (bOld bNew : Y → G)
    (hMatrix : ∀ x : X, ∀ y : Y,
      s (aNew x) * bNew y = s (aOld x) * bOld y)
    (x x0 : X) (y0 : Y) :
    aNew x * (aOld x)⁻¹ =
      aNew x0 * (aOld x0)⁻¹ := by
  have hratio (z : X) :
      (s (aNew z))⁻¹ * s (aOld z) =
        bNew y0 * (bOld y0)⁻¹ := by
    calc
      (s (aNew z))⁻¹ * s (aOld z) =
          (s (aNew z))⁻¹ *
            (s (aOld z) * bOld y0) * (bOld y0)⁻¹ := by group
      _ = (s (aNew z))⁻¹ *
            (s (aNew z) * bNew y0) * (bOld y0)⁻¹ := by
          rw [(hMatrix z y0).symm]
      _ = bNew y0 * (bOld y0)⁻¹ := by group
  apply s.rowRatio_eq_of_reverseRatio_eq
  exact (hratio x).trans (hratio x0).symm

/-- The SINGLE occupied-pair multiplier from manuscript (4.24)
exists and works on EVERY old row. Its reference choice only
affects the expression, not the resulting multiplier. -/
theorem exists_affineGauge_occupiedPairMultiplier
    (s : AffineAntiInvolution G)
    (aOld aNew : X → G)
    (bOld bNew : Y → G)
    (hMatrix : ∀ x : X, ∀ y : Y,
      s (aNew x) * bNew y = s (aOld x) * bOld y)
    (x0 : X) (y0 : Y) :
    ∃ M : G, ∀ x : X, M * aOld x = aNew x := by
  let M : G := aNew x0 * (aOld x0)⁻¹
  refine ⟨M, ?_⟩
  intro x
  have hratio : M = aNew x * (aOld x)⁻¹ :=
    (affineGauge_rowMultiplier_independent
      s aOld aNew bOld bNew hMatrix x x0 y0).symm
  calc
    M * aOld x = (aNew x * (aOld x)⁻¹) * aOld x := by
      rw [hratio]
    _ = aNew x := by group

end SemigenericEPPA
