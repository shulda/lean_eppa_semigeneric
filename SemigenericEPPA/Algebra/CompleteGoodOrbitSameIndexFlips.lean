import SemigenericEPPA.Algebra.GoodDefaultSkeletonOrbit

/-!
# Same-index swapped-edge safety needs only ONE complete good orbit

For a dense locally finite automorphism subgroup the expected algebraic
condition is weaker than full coherent EPPA: the good effective set
need only contain one whole affine congruence orbit.

The fixed-good-skeleton valuation construction uses a chosen genuinely
good seed g0 with s(g0)=g0. The critical same-old-index swapped pair
has effective colour
  s(a) * g0^(-1) * a.

Its entire family of such colours is in the congruence orbit of g0,
not merely in the orbit of an independently selected seed. The
argument combines the exact inverse-skeleton affine orbit identity
with the common gauge-middle congruence identity. No commutativity,
s(1)=1, or global good-set saturation is required.

This is a verified algebraic DLF gate only. It does NOT yet construct
a global finite group-action extension, a dense locally finite
subgroup, or establish the converse DLF criterion.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G]
variable {C : Type v}

/-- A chosen good skeleton seed with its ENTIRE congruence orbit good
has its affine inverse-skeleton seed good too. Unlike the coherent
version, no invariance of good effective colours in other orbits. -/
theorem RawDatum.good_inverseSkeletonSeed_of_completeOrbit
    (d : RawDatum G C)
    (g : G)
    (hGood : g ∈ d.selfReverseEffective)
    (hOrbit : ∀ b : G,
      congruence d.s b g ∈ d.selfReverseEffective) :
    d.s 1 * g⁻¹ ∈ d.selfReverseEffective := by
  have hFixed : d.s g = g :=
    d.selfReverseEffective_subset_fixed hGood
  have h := hOrbit (d.s 1 * g⁻¹)
  rw [congruence_inverse_fixed_skeleton_seed d.s g hFixed] at h
  exact h

/-- EVERY same-old-index swap colour s(a)*g^(-1)*a is in the
ONE preselected complete good orbit of g. This is the precise
inverse-skeleton branch of the nontrivial-G DLF raw-flip argument. -/
theorem RawDatum.good_swappedSameIndex_of_completeOrbit
    (d : RawDatum G C)
    (g : G)
    (hGood : g ∈ d.selfReverseEffective)
    (hOrbit : ∀ b : G,
      congruence d.s b g ∈ d.selfReverseEffective)
    (a : G) :
    d.s a * g⁻¹ * a ∈ d.selfReverseEffective := by
  have hFixed : d.s g = g :=
    d.selfReverseEffective_subset_fixed hGood
  have h := hOrbit
    ((d.s a * (d.s 1)⁻¹) * (d.s 1 * g⁻¹))
  rw [congruence_mul,
      congruence_inverse_fixed_skeleton_seed d.s g hFixed] at h
  have hMiddle :
      congruence d.s (d.s a * (d.s 1)⁻¹)
        (d.s 1 * g⁻¹) = d.s a * g⁻¹ * a := by
    simpa only [mul_one] using
      (congruence_commonGaugeMiddle d.s a 1 g⁻¹)
  rwa [hMiddle] at h

/-- A chosen complete good orbit provides one genuine good seed
and raw flip safety on the same-old-index witness pairs. This
packages the two facts for later DLF group-action constructions. -/
theorem RawDatum.exists_goodSkeleton_allSameIndexFlips
    (d : RawDatum G C)
    (hOrbit : d.HasCompleteGoodOrbit) :
    ∃ g : G,
      g ∈ d.selfReverseEffective ∧
      ∀ a : G,
        d.s a * g⁻¹ * a ∈ d.selfReverseEffective := by
  obtain ⟨g, hg, hall⟩ := hOrbit
  exact ⟨g, hg, fun a =>
    d.good_swappedSameIndex_of_completeOrbit g hg hall a⟩

end SemigenericEPPA
