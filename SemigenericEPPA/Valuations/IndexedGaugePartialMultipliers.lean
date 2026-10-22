import SemigenericEPPA.Structure.IndexedGauge
import SemigenericEPPA.Algebra.PartialGaugeFamilies

/-!
# Partial gauge multipliers for the ACTUAL prechosen indexed gauge

The ordinary effective EPPA proof previously constructed the
noncommutative partial-map multipliers only for the canonical
quotient-gauge of the auxiliary geometry. The nontrivial-G
coherent-positive fixed witness instead uses one preselected
constant-good IndexedGauge P on the actual quotient B/E. Its
old zero-section uses precisely P.vertexGauge.

For ANY injective partial E/F-isomorphism on an actual subset S
with a compatible permutation iota of the true class quotient,
we construct the partial multiplier m(i,j) for THIS gauge P.
The only prerequisites are exact P.effective=B.F on cross-E
pairs, literal quotient labels, and the already established
diagonal normalization a(x,[x])=1.

The resulting full (3.14)/(3.15) noncommutative affine identities
and neutral diagonal are exactly what the old partial-twist and
prescribed valuation automorphism gates consume.

No change of the fixed skeleton, gauge, old embedding or raw
cover; no F preservation on vertices outside the selected domain.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace IndexedGauge

/-- Any genuine selected partial E/F-isomorphism produces a
single compatible family of partial multipliers on the SAME
globally prechosen indexed gauge P (rather than the arbitrary
canonical quotient gauge of its effective geometry). -/
theorem exists_partialMultipliers_forActualGauge
    (D : EffectiveGeometry s V)
    (P : IndexedGauge s V (Quotient D.part))
    (hPLabel : ∀ x : V, P.label x = Quotient.mk D.part x)
    (hPF : ∀ x y : V, ¬D.part x y →
      P.effective x y = D.F x y)
    (hDiag : ∀ x : V, P.vertexGauge x (P.label x) = 1)
    (S : Set V) (p : S → V)
    (hE : ∀ x y : S,
      D.part x.val y.val ↔ D.part (p x) (p y))
    (hF : ∀ x y : S, ¬D.part x.val y.val →
      D.F (p x) (p y) = D.F x.val y.val)
    (iota : Equiv.Perm (Quotient D.part))
    (hIndex : ∀ x : S,
      Quotient.mk D.part (p x) =
        iota (Quotient.mk D.part x.val)) :
    ∃ m : Quotient D.part → Quotient D.part → G,
      (∀ (x : S) (j : Quotient D.part),
        (∃ y : S, Quotient.mk D.part y.val = j) →
        m (Quotient.mk D.part x.val) j *
          P.vertexGauge x.val j =
            P.vertexGauge (p x) (iota j)) ∧
      (∀ (i j : Quotient D.part),
        (∃ x : S, Quotient.mk D.part x.val = i) →
        (∃ y : S, Quotient.mk D.part y.val = j) →
        i ≠ j →
          s.normalized (m i j) *
              (P.skeleton (iota i) (iota j))⁻¹ * m j i =
                (P.skeleton i j)⁻¹) ∧
      (∀ i : Quotient D.part, m i i = 1) := by
  classical
  let cls : V → Quotient D.part := Quotient.mk D.part
  let a : V → Quotient D.part → G := P.vertexGauge
  let K : Quotient D.part → Quotient D.part → G := P.skeleton
  have hdiag (x : V) : a x (cls x) = 1 := by
    change P.vertexGauge x (Quotient.mk D.part x) = 1
    rw [← hPLabel x]
    exact hDiag x
  have hpart (x : S) : cls (p x) = iota (cls x.val) :=
    hIndex x
  have htarget (x : S) :
      P.label (p x) = iota (cls x.val) := by
    rw [hPLabel (p x)]
    exact hIndex x
  have hcolour (x y : S)
      (hxy : cls x.val ≠ cls y.val) :
      gaugeColour s (a x.val (cls y.val))
          (K (cls x.val) (cls y.val))
          (a y.val (cls x.val)) =
        gaugeColour s (a (p x) (iota (cls y.val)))
          (K (iota (cls x.val)) (iota (cls y.val)))
          (a (p y) (iota (cls x.val))) := by
    have hcross : ¬D.part x.val y.val := by
      intro h
      exact hxy (Quotient.sound h)
    have hcrossNew : ¬D.part (p x) (p y) := by
      intro hp
      exact hcross ((hE x y).mpr hp)
    have hlabelOld : P.label x.val ≠ P.label y.val := by
      rw [hPLabel x.val, hPLabel y.val]
      exact hxy
    have hlabelNew : P.label (p x) ≠ P.label (p y) := by
      rw [hPLabel (p x), hPLabel (p y)]
      intro heq
      exact hcrossNew (Quotient.exact heq)
    have hsource :
        gaugeColour s (a x.val (cls y.val))
          (K (cls x.val) (cls y.val))
          (a y.val (cls x.val)) = P.effective x.val y.val := by
      rw [P.effective_cross x.val y.val hlabelOld]
      rw [hPLabel x.val, hPLabel y.val]
    have htargetColour :
        P.effective (p x) (p y) =
          gaugeColour s (a (p x) (iota (cls y.val)))
            (K (iota (cls x.val)) (iota (cls y.val)))
            (a (p y) (iota (cls x.val))) := by
      rw [P.effective_cross (p x) (p y) hlabelNew]
      rw [htarget x, htarget y]
    calc
      gaugeColour s (a x.val (cls y.val))
          (K (cls x.val) (cls y.val))
          (a y.val (cls x.val)) =
        P.effective x.val y.val := hsource
      _ = D.F x.val y.val := hPF x.val y.val hcross
      _ = D.F (p x) (p y) := (hF x y hcross).symm
      _ = P.effective (p x) (p y) :=
        (hPF (p x) (p y) hcrossNew).symm
      _ = gaugeColour s (a (p x) (iota (cls y.val)))
          (K (iota (cls x.val)) (iota (cls y.val)))
          (a (p y) (iota (cls x.val))) := htargetColour
  let m : Quotient D.part → Quotient D.part → G :=
    partialGaugeMultiplier S p iota cls a
  obtain ⟨hinc, hcompat⟩ :=
    partialGaugeMultiplier_properties s S p iota cls a K
      hdiag hpart hcolour
  refine ⟨m, ?_, ?_, ?_⟩
  · exact hinc
  · exact hcompat
  · intro i
    exact partialGaugeMultiplier_diag S p iota cls a i

end IndexedGauge

end SemigenericEPPA
