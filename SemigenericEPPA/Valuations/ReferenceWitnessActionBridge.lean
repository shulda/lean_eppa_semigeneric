import SemigenericEPPA.Valuations.ReferencePartGroupAction
import SemigenericEPPA.Valuations.WitnessCocycleAction

/-!
# Reference-gauge actions and the whole valuation-witness cocycle API

The group action on witness parts built from reference-gauge ratios
in manuscript (4.27) must respect the old E-class fibres before
it can be used to transport the FULL two-layer valuation vertices.

We prove this compatibility from literal E-class equivariance of
the underlying real-label action, with no extra hypothesis about
the reference gauge. Thus the already certified general cocycle
transport theorem produces a genuine group action on all witness
vertices whenever suitable affine skeleton multipliers satisfying
their own cocycle have been supplied.

We also identify the exact additional condition for an old neutral
witness part to remain neutral: the reference gauge must be
equivariant at that target E-class. Without it, the group action
does not necessarily stabilize distinguished old vertices.

These are composition/typing bridges, not a claim that compatible
multipliers or coherent EPPA exist unconditionally.
-/

namespace SemigenericEPPA

universe u v w
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {s : AffineAntiInvolution G}

/-- The reference-gauge action has the chosen quotient-part action
as its first coordinate, regardless of reference valuations. -/
theorem referenceWitnessPartAction_class
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (h : H) (q : EffectiveWitnessPart D) :
    (referenceWitnessPartAction D rho iota z h q).1 = iota h q.1 := by
  rfl

/-- The two genuine group actions on old real labels and quotient
parts induce the fibre-compatibility required by the full witness
transport, with no extra constraint on the reference gauge. -/
theorem referenceWitnessPartAction_fibre_compat
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (h : H) (q : EffectiveWitnessPart D) (x : V) :
    (Quotient.mk D.part (rho h x) =
        (referenceWitnessPartAction D rho iota z h q).1) ↔
      (Quotient.mk D.part x = q.1) := by
  rw [referenceWitnessPartAction_class D rho iota z h q, hcls h x]
  constructor
  · intro heq
    exact (iota h).injective heq
  · intro heq
    exact congrArg (iota h) heq

/-- A distinguished neutral part stays neutral under the actual
reference-gauge group action whenever its reference gauge is
equivariant at that part. The condition is not automatic. -/
theorem referenceWitnessPartAction_neutral
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (h : H) (j : Quotient D.part)
    (hzinv : ∀ x : V,
      z (rho h x) (iota h j) = z x j) :
    referenceWitnessPartAction D rho iota z h
        (distinguishedWitnessPart D j) =
      distinguishedWitnessPart D (iota h j) := by
  have hL : ∀ x : V,
      referenceGaugeTwist rho iota z h x j = 1 := by
    intro x
    unfold referenceGaugeTwist
    rw [hzinv x]
    group
  exact twistedWitnessPartPerm_distinguished D
    (iota h) (rho h)
    (fun k x => referenceGaugeTwist rho iota z h x k) j hL

/-- With *additional* genuine skeleton cocycle multipliers, the
reference-gauge action on parts extends to a group homomorphism
on complete two-layer witness vertices, not just their quotient
or old-label coordinates. This is the exact composition of
the two independently certified abstract action constructions. -/
noncomputable def referenceWitnessCocycleAction
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (hmone : ∀ (q r : EffectiveWitnessPart D), q ≠ r →
      m 1 q r = 1)
    (hmmul : ∀ (k h : H) (q r : EffectiveWitnessPart D), q ≠ r →
      m (k * h) q r =
        m k (referenceWitnessPartAction D rho iota z h q)
            (referenceWitnessPartAction D rho iota z h r) *
          m h q r) :
    H →* Equiv.Perm (EffectiveWitnessVertex D) :=
  witnessCocycleAction D
    (referenceWitnessPartAction D rho iota z) rho
    (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
    m hmone hmmul

/-- The resulting full group action consists of actual effective
E/F-automorphisms when the pair multipliers satisfy the affine
skeleton identity. This leaves their construction as a separate
mathematical obligation. -/
theorem referenceWitnessCocycleAction_preserves_effective
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (hmone : ∀ (q r : EffectiveWitnessPart D), q ≠ r →
      m 1 q r = 1)
    (hmmul : ∀ (k h : H) (q r : EffectiveWitnessPart D), q ≠ r →
      m (k * h) q r =
        m k (referenceWitnessPartAction D rho iota z h q)
            (referenceWitnessPartAction D rho iota z h r) *
          m h q r)
    (hskeleton : ∀ (h : H) (q r : EffectiveWitnessPart D), q ≠ r →
      s.normalized (m h q r) *
        (K.colour
          (referenceWitnessPartAction D rho iota z h q)
          (referenceWitnessPartAction D rho iota z h r))⁻¹ *
        m h r q =
          (K.colour q r)⁻¹)
    (h : H) :
    (∀ X Y : EffectiveWitnessVertex D,
      K.toEffectiveGeometry.part
        (referenceWitnessCocycleAction D rho iota z hcls
          m hmone hmmul h X)
        (referenceWitnessCocycleAction D rho iota z hcls
          m hmone hmmul h Y) ↔
        K.toEffectiveGeometry.part X Y) ∧
    (∀ X Y : EffectiveWitnessVertex D,
      ¬K.toEffectiveGeometry.part X Y →
      K.toEffectiveGeometry.F
        (referenceWitnessCocycleAction D rho iota z hcls
          m hmone hmmul h X)
        (referenceWitnessCocycleAction D rho iota z hcls
          m hmone hmmul h Y) =
          K.toEffectiveGeometry.F X Y) := by
  exact witnessCocycleAction_preserves_effective
    D K (referenceWitnessPartAction D rho iota z) rho
    (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
    m hmone hmmul hskeleton h

end SemigenericEPPA
