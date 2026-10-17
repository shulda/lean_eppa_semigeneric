import SemigenericEPPA.Structure.IndexedGauge
import SemigenericEPPA.Structure.QuotientGaugeConverse

/-!
# Effective EPPA: the two valuation sorts and their incidence formula

For a given effective old structure D, a witness part is
    q = (i,h),       i ∈ V/E,  h : V → G.
A witness vertex is
    X = (q,x,χ),     [x]_E = i,
where χ has one group coordinate for each DIFFERENT witness part.

For the target witness part r=(j,g), the combined gauge coordinate is
    λ_X(r) = χ(r) * g(x).                                      (3.5)

The factor g(x) belongs to the TARGET PART r, NOT to the source
part q of X. The distinction is preserved literally in the Lean
definition below.

An arbitrary affine-reversal-compatible witness skeleton K equips
these carriers with a genuine group-valued rectangle geometry by
the already verified IndexedGauge construction. We prove the exact
effective-colour formula (3.6) and establish the intended embedding
of old vertex *data* into the two valuation layers.

No EPPA existence or automorphism extension theorem is claimed here.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- First valuation sort: an old E-class and a group-valued function
on all old vertices. -/
abbrev EffectiveWitnessPart (D : EffectiveGeometry s V) :=
  (Quotient D.part) × (V → G)

/-- The old zero/neutral part valuation. -/
def neutralPartValuation : V → G := fun _ => 1

/-- The copy of an old imaginary part used for the old embedding. -/
def distinguishedWitnessPart
    (D : EffectiveGeometry s V) (i : Quotient D.part) :
    EffectiveWitnessPart D :=
  ⟨i, neutralPartValuation⟩

/-- The distinguished witness part containing an old vertex x. -/
def oldWitnessPart
    (D : EffectiveGeometry s V) (x : V) :
    EffectiveWitnessPart D :=
  D.distinguishedWitnessPart (Quotient.mk D.part x)

/-- Second valuation sort: the old vertex label and its independent
vertex valuation towards EVERY other witness part. -/
structure EffectiveWitnessVertex (D : EffectiveGeometry s V) where
  part : EffectiveWitnessPart D
  old : V
  belongs : Quotient.mk D.part old = part.1
  vertexValuation : {r : EffectiveWitnessPart D // r ≠ part} → G

namespace EffectiveWitnessVertex

variable {D : EffectiveGeometry s V}

/-- Exact target-part incidence from manuscript (3.5).
The second factor is r.2 X.old; it is NOT X.part.2 X.old. -/
def crossIncidence
    (X : EffectiveWitnessVertex D)
    (r : EffectiveWitnessPart D) (hr : r ≠ X.part) : G :=
  X.vertexValuation ⟨r, hr⟩ * r.2 X.old

/-- A dummy 1 at the source part makes incidence total; values at
the source part are never used in cross-part effective colours. -/
noncomputable def incidence
    (X : EffectiveWitnessVertex D) (r : EffectiveWitnessPart D) : G := by
  classical
  exact if hr : r ≠ X.part then X.crossIncidence r hr else 1

theorem incidence_cross
    (X : EffectiveWitnessVertex D)
    (r : EffectiveWitnessPart D) (hr : r ≠ X.part) :
    X.incidence r = X.crossIncidence r hr := by
  simp [incidence, hr]

end EffectiveWitnessVertex

/-- Arbitrary skeleton colours between distinct blown-up parts,
with the affine reversal imposed exactly. -/
structure EffectiveWitnessSkeleton (D : EffectiveGeometry s V) where
  colour : EffectiveWitnessPart D → EffectiveWitnessPart D → G
  reverse :
    ∀ q r : EffectiveWitnessPart D,
      q ≠ r → colour r q = s (colour q r)

namespace EffectiveWitnessSkeleton

variable {D : EffectiveGeometry s V}
variable (K : EffectiveWitnessSkeleton D)

/-- The witness effective gauge system is indexed by actual
blown-up part valuations, without requiring their quotient by E. -/
noncomputable def toIndexedGauge :
    IndexedGauge s (EffectiveWitnessVertex D) (EffectiveWitnessPart D) where
  label := EffectiveWitnessVertex.part
  skeleton := K.colour
  skeleton_reverse := K.reverse
  vertexGauge := fun X r => X.incidence r

/-- Equation (3.6) immediately gives a genuine effective geometry,
including reversal and ALL noncommutative rectangle constraints. -/
noncomputable def toEffectiveGeometry :
    EffectiveGeometry s (EffectiveWitnessVertex D) :=
  K.toIndexedGauge.toEffectiveGeometry

@[simp] theorem witness_part_iff
    (X Y : EffectiveWitnessVertex D) :
    K.toEffectiveGeometry.part X Y ↔ X.part = Y.part :=
  Iff.rfl

/-- The exact effective-colour formula (3.6), with the target-part
valuation used in each of the two incidence coordinates. -/
theorem witness_cross_colour
    (X Y : EffectiveWitnessVertex D)
    (hXY : X.part ≠ Y.part) :
    K.toEffectiveGeometry.F X Y =
      gaugeColour s
        (X.crossIncidence Y.part hXY.symm)
        (K.colour X.part Y.part)
        (Y.crossIncidence X.part hXY) := by
  calc
    K.toEffectiveGeometry.F X Y =
      K.toIndexedGauge.effective X Y := rfl
    _ = gaugeColour s
      (X.incidence Y.part)
      (K.colour X.part Y.part)
      (Y.incidence X.part) :=
        K.toIndexedGauge.effective_cross X Y hXY
    _ = gaugeColour s
        (X.crossIncidence Y.part hXY.symm)
        (K.colour X.part Y.part)
        (Y.crossIncidence X.part hXY) := by
      rw [X.incidence_cross Y.part hXY.symm,
        Y.incidence_cross X.part hXY]

end EffectiveWitnessSkeleton

namespace EffectiveGeometry

variable (D : EffectiveGeometry s V)

/-- Old real vertex x with neutral part valuation h₀ and a vertex
valuation inherited from the old canonical quotient gauge. -/
noncomputable def oldWitnessVertex (x : V) :
    EffectiveWitnessVertex D where
  part := D.oldWitnessPart x
  old := x
  belongs := rfl
  vertexValuation := fun r => D.toQuotientGauge.vertexGauge x r.1.1

/-- The old real vertex label remains available verbatim in the
witness point, so the intended old embedding is injective. -/
theorem oldWitnessVertex_injective :
    Function.Injective D.oldWitnessVertex := by
  intro x y h
  exact congrArg (fun X : EffectiveWitnessVertex D => X.old) h

/-- Two different old E-classes embed into different distinguished
witness parts; distinct old parts are not collapsed. -/
theorem oldWitnessPart_ne (x y : V)
    (hxy : ¬D.part x y) :
    D.oldWitnessPart x ≠ D.oldWitnessPart y := by
  intro h
  have hc : Quotient.mk D.part x = Quotient.mk D.part y :=
    congrArg (fun q : EffectiveWitnessPart D => q.1) h
  exact hxy (Quotient.exact hc)

/-- At a target with neutral part valuation, the old embedded point's
combined incidence is the original old gauge coordinate. -/
theorem oldWitnessVertex_crossIncidence (x y : V)
    (hr : D.oldWitnessPart y ≠ D.oldWitnessPart x) :
    (D.oldWitnessVertex x).crossIncidence
      (D.oldWitnessPart y) hr =
      D.toQuotientGauge.vertexGauge x (Quotient.mk D.part y) := by
  simp [EffectiveWitnessVertex.crossIncidence,
    oldWitnessVertex, oldWitnessPart, distinguishedWitnessPart,
    neutralPartValuation]

end EffectiveGeometry

end SemigenericEPPA
