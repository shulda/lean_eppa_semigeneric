import SemigenericEPPA.Valuations.PrescribedMultiplierAutomorphisms
import SemigenericEPPA.Valuations.OldVertexExtensionCriterion
import Mathlib.Tactic.Group

/-!
# Homomorphic action on the full effective valuation witness

Let H act homomorphically on witness parts Q and old real labels V.
Assume that the two actions respect the old E-class fibres. If
ordered-pair multipliers m_h(q,r) satisfy

  m_1(q,r)=1,
  m_(kh)(q,r)=m_k(sigma_h q,sigma_h r) m_h(q,r),

then the *actual invertible* witness-coordinate transports
T_h from (3.11) form a homomorphism H -> Perm(witness vertices).

We prove the group law via the uniquely determining data: part,
real label, and all target-part incidence coordinates. This avoids
false coherence claims based solely on independently existing
automorphisms.

If the multipliers also satisfy the affine/noncommutative
skeleton equation (3.9) for each h, this homomorphism acts by
genuine E/F-automorphisms of the effective valuation geometry.

This supplies the vertex-level cocycle-composition gate for the
full-group effective lift of the manuscript, but does not assert
the existence of multipliers satisfying the hypotheses.
-/

namespace SemigenericEPPA

universe u v w

variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {s : AffineAntiInvolution G}

/-- The action of an old-label permutation restricts to exact
bijections of each labelled witness part's old E-class fibre. -/
def groupWitnessFibreEquiv
    (D : EffectiveGeometry s V)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (h : H) (q : EffectiveWitnessPart D) :
    EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (sigma h q) where
  toFun := fun x =>
    ⟨pi h x.val, (hcompat h q x.val).mpr x.property⟩
  invFun := fun y =>
    ⟨(pi h).symm y.val, (hcompat h q ((pi h).symm y.val)).mp
      (by simpa only [Equiv.apply_symm_apply] using y.property)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact (pi h).symm_apply_apply x.val
  right_inv := by
    intro y
    apply Subtype.ext
    exact (pi h).apply_symm_apply y.val

/-- The chosen group action and pair multipliers produce a genuine
permutation of the complete two-layer witness carrier. -/
def witnessCocyclePerm
    (D : EffectiveGeometry s V)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (h : H) : Equiv.Perm (EffectiveWitnessVertex D) :=
  witnessAutomorphismWithMultipliers D (sigma h)
    (groupWitnessFibreEquiv D sigma pi hcompat h) (m h)

@[simp] theorem witnessCocyclePerm_part
    (D : EffectiveGeometry s V)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (h : H) (X : EffectiveWitnessVertex D) :
    (witnessCocyclePerm D sigma pi hcompat m h X).part =
      sigma h X.part :=
  witnessAutomorphismWithMultipliers_part D (sigma h)
    (groupWitnessFibreEquiv D sigma pi hcompat h) (m h) X

@[simp] theorem witnessCocyclePerm_old
    (D : EffectiveGeometry s V)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (h : H) (X : EffectiveWitnessVertex D) :
    (witnessCocyclePerm D sigma pi hcompat m h X).old =
      pi h X.old := by
  simpa only [witnessCocyclePerm, groupWitnessFibreEquiv] using
    (witnessAutomorphismWithMultipliers_old
      D (sigma h) (groupWitnessFibreEquiv D sigma pi hcompat h)
        (m h) X)

theorem witnessCocyclePerm_incidence
    (D : EffectiveGeometry s V)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (h : H) (X : EffectiveWitnessVertex D)
    (r : EffectiveWitnessPart D) (hr : r ≠ X.part) :
    (witnessCocyclePerm D sigma pi hcompat m h X).crossIncidence
        (sigma h r) (by
          intro heq
          exact hr ((sigma h).injective
            (heq.trans (witnessCocyclePerm_part
              D sigma pi hcompat m h X).symm))) =
      m h X.part r * X.crossIncidence r hr := by
  simpa only [witnessCocyclePerm] using
    (witnessAutomorphismWithMultipliers_incidence
      D (sigma h)
      (groupWitnessFibreEquiv D sigma pi hcompat h)
      (m h) X r hr)

/-- When the chosen multipliers have the group-law cocycle, the
complete transported witness vertex for kh is literally the
successive transport by h and then k. -/
theorem witnessCocyclePerm_mul_apply
    (D : EffectiveGeometry s V)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (hmmul : ∀ (k h : H) (q r : EffectiveWitnessPart D), q ≠ r →
      m (k * h) q r =
        m k (sigma h q) (sigma h r) * m h q r)
    (k h : H) (X : EffectiveWitnessVertex D) :
    witnessCocyclePerm D sigma pi hcompat m (k * h) X =
      witnessCocyclePerm D sigma pi hcompat m k
        (witnessCocyclePerm D sigma pi hcompat m h X) := by
  let T := witnessCocyclePerm D sigma pi hcompat m
  let Y := T h X
  apply EffectiveWitnessVertex.eq_of_crossIncidence (T (k * h) X) (T k Y)
  · calc
      (T (k * h) X).part = sigma (k * h) X.part :=
        witnessCocyclePerm_part D sigma pi hcompat m (k * h) X
      _ = sigma k (sigma h X.part) := by rw [map_mul]; rfl
      _ = sigma k Y.part := by
        rw [witnessCocyclePerm_part D sigma pi hcompat m h X]
      _ = (T k Y).part :=
        (witnessCocyclePerm_part D sigma pi hcompat m k Y).symm
  · calc
      (T (k * h) X).old = pi (k * h) X.old :=
        witnessCocyclePerm_old D sigma pi hcompat m (k * h) X
      _ = pi k (pi h X.old) := by rw [map_mul]; rfl
      _ = pi k Y.old := by
        rw [witnessCocyclePerm_old D sigma pi hcompat m h X]
      _ = (T k Y).old :=
        (witnessCocyclePerm_old D sigma pi hcompat m k Y).symm
  · intro r hrL hrR
    let u : EffectiveWitnessPart D := (sigma (k * h)).symm r
    have hru : sigma (k * h) u = r :=
      (sigma (k * h)).apply_symm_apply r
    have hσ : sigma k (sigma h u) = r := by
      calc
        sigma k (sigma h u) = sigma (k * h) u := by
          rw [map_mul]; rfl
        _ = r := hru
    have hu : u ≠ X.part := by
      intro heq
      apply hrL
      calc
        r = sigma (k * h) u := hru.symm
        _ = sigma (k * h) X.part := congrArg (sigma (k * h)) heq
        _ = (T (k * h) X).part :=
          (witnessCocyclePerm_part D sigma pi hcompat m (k * h) X).symm
    have huY : sigma h u ≠ Y.part := by
      rw [witnessCocyclePerm_part D sigma pi hcompat m h X]
      exact (sigma h).injective.ne hu
    have htotal :=
      witnessCocyclePerm_incidence D sigma pi hcompat m
        (k * h) X u hu
    have hfirst :=
      witnessCocyclePerm_incidence D sigma pi hcompat m
        h X u hu
    have hsecond :=
      witnessCocyclePerm_incidence D sigma pi hcompat m
        k Y (sigma h u) huY
    have hM : m (k * h) X.part u =
        m k Y.part (sigma h u) * m h X.part u := by
      calc
        m (k * h) X.part u =
            m k (sigma h X.part) (sigma h u) * m h X.part u :=
              hmmul k h X.part u hu
        _ = m k Y.part (sigma h u) * m h X.part u := by
          rw [witnessCocyclePerm_part D sigma pi hcompat m h X]
    have hLeft :
        (T (k * h) X).crossIncidence r hrL =
          m (k * h) X.part u * X.crossIncidence u hu := by
      simpa only [hru] using htotal
    have hRight :
        (T k Y).crossIncidence r hrR =
          (m k Y.part (sigma h u) * m h X.part u) *
            X.crossIncidence u hu := by
      calc
        (T k Y).crossIncidence r hrR =
            m k Y.part (sigma h u) *
              Y.crossIncidence (sigma h u) huY := by
                simpa only [hσ] using hsecond
        _ = (m k Y.part (sigma h u) * m h X.part u) *
            X.crossIncidence u hu := by
              rw [hfirst]
              group
    calc
      (T (k * h) X).crossIncidence r hrL =
          m (k * h) X.part u * X.crossIncidence u hu := hLeft
      _ = (m k Y.part (sigma h u) * m h X.part u) *
          X.crossIncidence u hu := by rw [hM]
      _ = (T k Y).crossIncidence r hrR := hRight.symm

/-- The identity multiplier 1 and the cocycle on cross-part pairs
make the witness-vertex transports a *genuine group homomorphism*. -/
noncomputable def witnessCocycleAction
    (D : EffectiveGeometry s V)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (hmone : ∀ (q r : EffectiveWitnessPart D), q ≠ r → m 1 q r = 1)
    (hmmul : ∀ (k h : H) (q r : EffectiveWitnessPart D), q ≠ r →
      m (k * h) q r =
        m k (sigma h q) (sigma h r) * m h q r) :
    H →* Equiv.Perm (EffectiveWitnessVertex D) where
  toFun := witnessCocyclePerm D sigma pi hcompat m
  map_one' := by
    apply Equiv.ext
    intro X
    apply EffectiveWitnessVertex.eq_of_crossIncidence
      (witnessCocyclePerm D sigma pi hcompat m 1 X) X
    · simp only [witnessCocyclePerm_part, map_one,
        Equiv.Perm.one_apply]
    · simp only [witnessCocyclePerm_old, map_one,
        Equiv.Perm.one_apply]
    · intro r hrT hrX
      have h := witnessCocyclePerm_incidence D sigma pi hcompat m
        1 X r hrX
      have hs : sigma (1 : H) r = r := by simp
      have hresult :
          (witnessCocyclePerm D sigma pi hcompat m 1 X).crossIncidence
            r hrT = m 1 X.part r * X.crossIncidence r hrX := by
              simpa only [hs] using h
      rw [hresult, hmone X.part r hrX, one_mul]
  map_mul' := by
    intro k h
    apply Equiv.ext
    intro X
    change witnessCocyclePerm D sigma pi hcompat m (k * h) X =
      (witnessCocyclePerm D sigma pi hcompat m k *
       witnessCocyclePerm D sigma pi hcompat m h) X
    rw [Equiv.Perm.mul_apply]
    exact witnessCocyclePerm_mul_apply D sigma pi hcompat m hmmul k h X

/-- Add the old (3.9) skeleton equation: each group element is
not just a permutation but a literal E/F automorphism of the
same effective witness geometry. -/
theorem witnessCocycleAction_preserves_effective
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (hmone : ∀ (q r : EffectiveWitnessPart D), q ≠ r → m 1 q r = 1)
    (hmmul : ∀ (k h : H) (q r : EffectiveWitnessPart D), q ≠ r →
      m (k * h) q r =
        m k (sigma h q) (sigma h r) * m h q r)
    (hskeleton : ∀ (h : H) (q r : EffectiveWitnessPart D), q ≠ r →
      s.normalized (m h q r) * (K.colour (sigma h q) (sigma h r))⁻¹ *
        m h r q = (K.colour q r)⁻¹)
    (h : H) :
    (∀ X Y : EffectiveWitnessVertex D,
      K.toEffectiveGeometry.part
        (witnessCocycleAction D sigma pi hcompat m hmone hmmul h X)
        (witnessCocycleAction D sigma pi hcompat m hmone hmmul h Y) ↔
        K.toEffectiveGeometry.part X Y) ∧
    (∀ X Y : EffectiveWitnessVertex D,
      ¬K.toEffectiveGeometry.part X Y →
      K.toEffectiveGeometry.F
        (witnessCocycleAction D sigma pi hcompat m hmone hmmul h X)
        (witnessCocycleAction D sigma pi hcompat m hmone hmmul h Y) =
          K.toEffectiveGeometry.F X Y) := by
  constructor
  · exact witnessAutomorphismWithMultipliers_part_iff
      D K (sigma h)
      (groupWitnessFibreEquiv D sigma pi hcompat h) (m h)
  · intro X Y hXY
    exact witnessAutomorphismWithMultipliers_colour
      D K (sigma h)
      (groupWitnessFibreEquiv D sigma pi hcompat h)
      (m h) (hskeleton h) X Y hXY

end SemigenericEPPA
