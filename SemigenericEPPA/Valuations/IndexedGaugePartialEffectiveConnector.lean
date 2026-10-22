import SemigenericEPPA.Valuations.TwistedIndexedGaugeOldVertexExtension
import SemigenericEPPA.Valuations.IndexedGaugePartialMultipliers

/-!
# Individual effective partial connectors on ONE fixed indexed-gauge witness

The existing noncommutative old-partial multiplier family works for
a globally selected indexed gauge R, rather than replacing it by the
canonical quotient-gauge. The full twisted witness automorphism
constructed from these multipliers likewise extends the literal
gauge-valued old zero-section and preserves the fixed skeleton K.

For ANY genuine partial E/F-isomorphism p:S→D and a compatible
permutation of the auxiliary real labels / actual E-classes,
the noncommutative (3.14)/(3.15) equations and the full
(3.16)--(3.19) witness construction now compose with no extra
multiplier, twist or incidence assumptions.

This is exactly the effective individual-connector input to the
ALREADY fixed raw cover J. It keeps K, R and the old embedding
independent of the particular connector p. There is no
claim of raw-colour preservation until the fixed-cover lift.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace IndexedGauge

/-- A single prechosen E/F gauge R with diagonal one and fixed
compatible valuation skeleton K supports EVERY individual selected
old effective partial connector, provided its induced E-class
and auxiliary real-label partial injection has been extended.

No gauge row/multiplier/exact incidence choices remain in the
conclusion: all are produced from actual E/F preservation. -/
theorem exists_effectivePartialConnector_onFixedGauge
    (D : EffectiveGeometry s V)
    (R : IndexedGauge s V (Quotient D.part))
    (hLabel : ∀ x : V, R.label x = Quotient.mk D.part x)
    (hRF : ∀ x y : V, ¬D.part x y →
      R.effective x y = D.F x y)
    (hDiag : ∀ x : V,
      R.vertexGauge x (R.label x) = 1)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (hK : ∀ i j : Quotient D.part, i ≠ j →
      K.colour (distinguishedWitnessPart D i)
        (distinguishedWitnessPart D j) = R.skeleton i j)
    (S : Set V) (p : S → V)
    (hE : ∀ x y : S,
      D.part x.val y.val ↔ D.part (p x) (p y))
    (hF : ∀ x y : S, ¬D.part x.val y.val →
      D.F (p x) (p y) = D.F x.val y.val)
    (iota : Equiv.Perm (Quotient D.part))
    (pi : Equiv.Perm V)
    (hPi : ∀ z : V,
      Quotient.mk D.part (pi z) =
        iota (Quotient.mk D.part z))
    (hOld : ∀ x : S, pi x.val = p x) :
    ∃ theta : Equiv.Perm (EffectiveWitnessVertex D),
      (∀ x : S,
        theta (D.gaugeOldWitnessVertex R.vertexGauge x.val) =
          D.gaugeOldWitnessVertex R.vertexGauge (p x)) ∧
      (∀ X Y : EffectiveWitnessVertex D,
        K.toEffectiveGeometry.part (theta X) (theta Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ X Y : EffectiveWitnessVertex D,
        ¬K.toEffectiveGeometry.part X Y →
          K.toEffectiveGeometry.F (theta X) (theta Y) =
            K.toEffectiveGeometry.F X Y) := by
  have hIndex (x : S) :
      Quotient.mk D.part (p x) =
        iota (Quotient.mk D.part x.val) := by
    rw [← hOld x]
    exact hPi x.val
  obtain ⟨m, hInc, hCompat, _hDiagM⟩ :=
    R.exists_partialMultipliers_forActualGauge
      D hLabel hRF hDiag S p hE hF iota hIndex
  exact exists_twistedIndexedGaugeWitnessAutomorphism_extending_old
    D K R hK S p iota pi hPi hOld m hInc hCompat

end IndexedGauge

end SemigenericEPPA
