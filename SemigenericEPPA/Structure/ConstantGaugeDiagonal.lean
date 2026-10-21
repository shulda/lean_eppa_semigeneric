import SemigenericEPPA.Structure.ConstantSkeletonGauge
import SemigenericEPPA.Structure.CanonicalDiagonalGauge
import SemigenericEPPA.Valuations.ConstantSkeletonOldEmbedding

/-!
# Diagonal gauge normalization survives constant-skeleton recoding

The canonical effective E-rectangle geometry coming from the literal
R1--R3 language has same-class dummy F=1, so a(x,[x])=1. The
constant-good-skeleton reparametrization of the old gauge changes
only coordinates a(x,j) with j < [x], and never touches j=[x].

Consequently the recoded fixed-skeleton old embedding STILL has
diagonal gauge 1. This checks the only additional old-coordinate
normalization used by the selected-subset multipliers.

Without this bridge, the relative coherent-positive formalization
could silently assume a property of an arbitrary gauge that only
holds for the chosen canonical/recoded presentation.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- The constant-skeleton transformation leaves EACH old gauge
entry at its own E-index untouched, no matter what the other
skeleton entries or affine reversal are. -/
theorem IndexedGauge.constantSkeletonGauge_diagonal
    {I : Type w}
    (P : IndexedGauge s V I) [LinearOrder I]
    (g0 : G) (hfixed : s g0 = g0) (x : V) :
    (P.constantSkeletonGauge g0 hfixed).vertexGauge x
      ((P.constantSkeletonGauge g0 hfixed).label x) =
        P.vertexGauge x (P.label x) := by
  simp [IndexedGauge.constantSkeletonGauge]

namespace EffectiveGeometry

/-- In a normalized effective geometry, the actual CONSTANT-skeleton
quotient-indexed gauge used for the distinguished old embedding
remains normalized on all diagonal old coordinates. -/
theorem constantQuotientIndexedGauge_diagonal_one
    (D : EffectiveGeometry s V)
    [LinearOrder (Quotient D.part)]
    (hSame : ∀ x y : V, D.part x y → D.F x y = 1)
    (g0 : G) (hfixed : s g0 = g0) (x : V) :
    (D.constantQuotientIndexedGauge g0 hfixed).vertexGauge x
      ((D.constantQuotientIndexedGauge g0 hfixed).label x) = 1 := by
  letI : LinearOrder (Quotient D.toQuotientGauge.part) :=
    (inferInstance : LinearOrder (Quotient D.part))
  calc
    (D.constantQuotientIndexedGauge g0 hfixed).vertexGauge x
        ((D.constantQuotientIndexedGauge g0 hfixed).label x) =
      (IndexedGauge.ofQuotientGauge D.toQuotientGauge).vertexGauge x
        ((IndexedGauge.ofQuotientGauge D.toQuotientGauge).label x) := by
        exact IndexedGauge.constantSkeletonGauge_diagonal
          (IndexedGauge.ofQuotientGauge D.toQuotientGauge) g0 hfixed x
    _ = D.toQuotientGauge.vertexGauge x (Quotient.mk D.part x) := rfl
    _ = 1 := D.quotientGauge_diagonal_one hSame x

end EffectiveGeometry

end SemigenericEPPA
