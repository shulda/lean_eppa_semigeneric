import SemigenericEPPA.Valuations.OldEmbedding

/-!
# Existence of the effective witness skeleton with the old neutral copy

The two-layer valuation carrier (q=(i,h), X=(q,x,χ)) requires an
arbitrary skeleton between distinct witness parts satisfying affine
reversal. On the neutral witness parts (i,h₀) we must retain the old
skeleton K^A_ij to embed A.

Choose any linear order on the witness-part type. For distinct q,r:
* if both part valuations are neutral, use the OLD skeleton;
* otherwise, use 1 in increasing order and s(1) in reverse order.

This proves the required skeleton always exists once the witness
parts have an auxiliary linear order. In the finite EPPA theorem
such an order can be chosen on the finite witness-part type.
The skeleton agrees exactly with the old one and therefore the
neutral old copy embeds into the effective witness.

No self-reversing raw colour is needed. No claim of EPPA automorphism
extensions is made here.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- A concrete skeleton with an arbitrary auxiliary ordering of
blown-up witness parts. The diagonal value 1 is irrelevant. -/
noncomputable def orderedWitnessSkeleton
    (D : EffectiveGeometry s V)
    [LinearOrder (EffectiveWitnessPart D)]
    (q r : EffectiveWitnessPart D) : G := by
  classical
  exact if q = r then 1
    else if q.2 = neutralPartValuation ∧
        r.2 = neutralPartValuation then
      D.toQuotientGauge.skeleton q.1 r.1
    else if q < r then 1 else s 1

/-- Affine reversal of the ordered skeleton, including the
nontrivial t=s(1) when it need not be 1. -/
theorem orderedWitnessSkeleton_reverse
    (D : EffectiveGeometry s V)
    [LinearOrder (EffectiveWitnessPart D)]
    (q r : EffectiveWitnessPart D) (hqr : q ≠ r) :
    orderedWitnessSkeleton D r q =
      s (orderedWitnessSkeleton D q r) := by
  classical
  have hrq : r ≠ q := Ne.symm hqr
  by_cases hn : q.2 = neutralPartValuation ∧
      r.2 = neutralPartValuation
  · have hnr : r.2 = neutralPartValuation ∧
        q.2 = neutralPartValuation := ⟨hn.2, hn.1⟩
    have hclasses : q.1 ≠ r.1 := by
      intro h
      apply hqr
      apply Prod.ext
      · exact h
      · exact hn.1.trans hn.2.symm
    have hs := D.toQuotientGauge.skeleton_reverse q.1 r.1 hclasses
    simpa [orderedWitnessSkeleton, hqr, hrq, hn, hnr] using hs
  · have hnr : ¬(r.2 = neutralPartValuation ∧
        q.2 = neutralPartValuation) := by
      rintro ⟨hr, hq⟩
      exact hn ⟨hq, hr⟩
    rcases lt_or_gt_of_ne hqr with hlt | hgt
    · have hnlt : ¬r < q := not_lt_of_ge (le_of_lt hlt)
      simp [orderedWitnessSkeleton, hqr, hrq, hn, hnr, hlt, hnlt]
    · have hnlt : ¬q < r := not_lt_of_ge (le_of_lt hgt)
      simpa [orderedWitnessSkeleton, hqr, hrq, hn, hnr, hgt, hnlt]
        using (s.involutive 1).symm

/-- A genuine witness skeleton in the exact existing API. -/
noncomputable def EffectiveGeometry.orderedSkeleton
    (D : EffectiveGeometry s V)
    [LinearOrder (EffectiveWitnessPart D)] :
    EffectiveWitnessSkeleton D where
  colour := orderedWitnessSkeleton D
  reverse := orderedWitnessSkeleton_reverse D

/-- The new skeleton reproduces the original one *literally* on all
pairs of distinct distinguished neutral witness parts. -/
theorem EffectiveGeometry.orderedSkeleton_extendsOld
    (D : EffectiveGeometry s V)
    [LinearOrder (EffectiveWitnessPart D)] :
    D.orderedSkeleton.ExtendsOldSkeleton D := by
  intro i j hij
  have hparts :
      distinguishedWitnessPart D i ≠
        distinguishedWitnessPart D j := by
    intro h
    apply hij
    exact congrArg (fun q : EffectiveWitnessPart D => q.1) h
  change orderedWitnessSkeleton D
      (distinguishedWitnessPart D i)
      (distinguishedWitnessPart D j) =
        D.toQuotientGauge.skeleton i j
  have hpair :
      (i, (neutralPartValuation : V → G)) ≠
        (j, (neutralPartValuation : V → G)) := by
    intro h
    exact hij (congrArg Prod.fst h)
  change (if (i, (neutralPartValuation : V → G)) =
       (j, (neutralPartValuation : V → G)) then (1 : G)
       else D.toQuotientGauge.skeleton i j) =
       D.toQuotientGauge.skeleton i j
  simp [hpair]

/-- The old embedding into the ordered effective witness preserves
every cross-part effective group colour and is injective. The first
EPPA witness construction gate is now instantiated with one concrete
skeleton, rather than assumed skeleton data. -/
theorem EffectiveGeometry.orderedSkeleton_oldColours
    (D : EffectiveGeometry s V)
    [LinearOrder (EffectiveWitnessPart D)]
    (x y : V) (hxy : ¬D.part x y) :
    D.orderedSkeleton.toEffectiveGeometry.F
      (D.oldWitnessVertex x) (D.oldWitnessVertex y) =
        D.F x y :=
  D.oldWitnessVertex_colour D.orderedSkeleton
    D.orderedSkeleton_extendsOld x y hxy

end SemigenericEPPA
