import SemigenericEPPA.Structure.IndexedGauge
import SemigenericEPPA.Algebra.SkeletonMultipliers

/-!
# Explicit effective gauge-automorphism criterion

A vertex permutation τ and part-label permutation σ preserve an
indexed effective group-valued rectangle geometry provided their
gauge coordinates transform by left multipliers m(i,j), and these
multipliers obey the affine/noncommutative skeleton constraint

  t⁻¹ s(m(i,j)) K(σi,σj)⁻¹ m(j,i) = K(i,j)⁻¹,

exactly the criterion (2.8)/(3.9) in the manuscript.

We prove that the E-equivalence relation is preserved/reflected and
that EVERY cross-part effective colour F is preserved verbatim.
This is the abstract automorphism-correctness component of the
effective EPPA witness construction; the later valuation mechanism
must produce such τ,σ,m for each partial automorphism.

No finiteness, group commutativity, S-saturation or HKN theorem.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {V : Type v} {I : Type w}
variable {s : AffineAntiInvolution G}

/-- Concrete data for a gauge-preserving automorphism of a
label-indexed effective rectangle geometry. It is deliberately
phrased in terms of ordinary permutations and equations, so it
can be instantiated by the two-layer valuation witness later. -/
structure IndexedGaugeAutomorphism
    (P : IndexedGauge s V I) where
  partPermutation : I ≃ I
  vertexPermutation : V ≃ V
  labels : ∀ x : V,
    P.label (vertexPermutation x) = partPermutation (P.label x)
  multipliers : I → I → G
  coordinates :
    ∀ (x : V) (j : I), P.label x ≠ j →
      P.vertexGauge (vertexPermutation x) (partPermutation j) =
        multipliers (P.label x) j * P.vertexGauge x j
  skeleton :
    ∀ i j : I, i ≠ j →
      s.normalized (multipliers i j) *
        (P.skeleton (partPermutation i) (partPermutation j))⁻¹ *
          multipliers j i = (P.skeleton i j)⁻¹

namespace IndexedGaugeAutomorphism

variable {P : IndexedGauge s V I}
variable (T : IndexedGaugeAutomorphism P)

/-- The vertex permutation preserves and reflects exactly the
E-relation (same part label), not merely its number of parts. -/
theorem part_iff (x y : V) :
    P.toEffectiveGeometry.part (T.vertexPermutation x)
      (T.vertexPermutation y) ↔
    P.toEffectiveGeometry.part x y := by
  change P.label (T.vertexPermutation x) =
    P.label (T.vertexPermutation y) ↔ P.label x = P.label y
  rw [T.labels x, T.labels y]
  constructor
  · intro h
    exact T.partPermutation.injective h
  · intro h
    exact congrArg T.partPermutation h

/-- Equation (3.9) guarantees every effective cross-part colour
is unchanged by the prescribed vertex permutation. -/
theorem colour_of_cross
    (x y : V) (hxy : ¬P.toEffectiveGeometry.part x y) :
    P.toEffectiveGeometry.F (T.vertexPermutation x)
      (T.vertexPermutation y) =
    P.toEffectiveGeometry.F x y := by
  have hij : P.label x ≠ P.label y := hxy
  have htr : P.label (T.vertexPermutation x) ≠
      P.label (T.vertexPermutation y) := by
    rw [T.labels x, T.labels y]
    intro heq
    exact hij (T.partPermutation.injective heq)
  calc
    P.toEffectiveGeometry.F (T.vertexPermutation x)
        (T.vertexPermutation y) =
      gaugeColour s
        (P.vertexGauge (T.vertexPermutation x)
          (P.label (T.vertexPermutation y)))
        (P.skeleton (P.label (T.vertexPermutation x))
          (P.label (T.vertexPermutation y)))
        (P.vertexGauge (T.vertexPermutation y)
          (P.label (T.vertexPermutation x))) :=
            P.effective_cross
              (T.vertexPermutation x) (T.vertexPermutation y) htr
    _ = gaugeColour s
        (T.multipliers (P.label x) (P.label y) *
          P.vertexGauge x (P.label y))
        (P.skeleton (T.partPermutation (P.label x))
          (T.partPermutation (P.label y)))
        (T.multipliers (P.label y) (P.label x) *
          P.vertexGauge y (P.label x)) := by
            rw [T.labels x, T.labels y,
              T.coordinates x (P.label y) hij,
              T.coordinates y (P.label x) hij.symm]
    _ = gaugeColour s
        (P.vertexGauge x (P.label y))
        (P.skeleton (P.label x) (P.label y))
        (P.vertexGauge y (P.label x)) := by
            exact eppe_multiplier_preserves_gaugeColour
              s (P.skeleton (P.label x) (P.label y))
                (P.skeleton (T.partPermutation (P.label x))
                  (T.partPermutation (P.label y)))
                (T.multipliers (P.label x) (P.label y))
                (T.multipliers (P.label y) (P.label x))
                (P.vertexGauge x (P.label y))
                (P.vertexGauge y (P.label x))
                (T.skeleton (P.label x) (P.label y) hij)
    _ = P.toEffectiveGeometry.F x y :=
      (P.effective_cross x y hij).symm

/-- The effective group-valued rectangle geometry has an
automorphism in the concrete sense: E and every cross-part
group colour are preserved by a bijection of real vertices. -/
theorem isEffectiveAutomorphism :
    (∀ x y,
      P.toEffectiveGeometry.part (T.vertexPermutation x)
        (T.vertexPermutation y) ↔
          P.toEffectiveGeometry.part x y) ∧
    (∀ x y, ¬P.toEffectiveGeometry.part x y →
      P.toEffectiveGeometry.F (T.vertexPermutation x)
        (T.vertexPermutation y) =
          P.toEffectiveGeometry.F x y) :=
  ⟨T.part_iff, T.colour_of_cross⟩

end IndexedGaugeAutomorphism
end SemigenericEPPA
