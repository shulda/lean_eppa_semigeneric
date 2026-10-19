import SemigenericEPPA.Valuations.WitnessCocycleAction

/-!
# Group actions on the witness under an invariant skeleton

When a given H-action on witness parts Q preserves a chosen witness
skeleton K literally, the pairwise multipliers can all be taken to be
1. Their identity, noncommutative cocycle and affine skeleton
compatibility equations then hold automatically.

Consequently, every compatible H-action on old real labels extends
to a genuine group action on ALL two-layer effective witness vertices,
preserving E and every effective colour F. This is a useful sufficient
criterion for coherent constructions, particularly the sector with
a singleton effective group, but invariant K is an actual hypothesis
and is not provided for arbitrary H.

The theorem proves no existence of such a witness-part action or
invariant skeleton and no coherent partial-isomorphism groupoid
assignment by itself.
-/

namespace SemigenericEPPA

universe u v w
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {s : AffineAntiInvolution G}

/-- When the part action and the real-label action preserve the
same E-classes, the universal neutral multiplier 1 has exact
identity and group cocycle equations. -/
noncomputable def invariantSkeletonWitnessAction
    (D : EffectiveGeometry s V)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1)) :
    H →* Equiv.Perm (EffectiveWitnessVertex D) :=
  witnessCocycleAction D sigma pi hcompat
    (fun _ _ _ => 1)
    (by intros; rfl)
    (by intros; simp)

/-- Literal invariance of the chosen skeleton makes the neutral
multiplier satisfy the exact affine skeleton condition, including
nontrivial affine reversal s(1) and noncommutative group G. -/
theorem invariantSkeletonWitnessAction_preserves_effective
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (hK : ∀ (h : H) (q r : EffectiveWitnessPart D), q ≠ r →
      K.colour (sigma h q) (sigma h r) = K.colour q r)
    (h : H) :
    (∀ X Y : EffectiveWitnessVertex D,
      K.toEffectiveGeometry.part
        (invariantSkeletonWitnessAction D sigma pi hcompat h X)
        (invariantSkeletonWitnessAction D sigma pi hcompat h Y) ↔
        K.toEffectiveGeometry.part X Y) ∧
    (∀ X Y : EffectiveWitnessVertex D,
      ¬K.toEffectiveGeometry.part X Y →
      K.toEffectiveGeometry.F
        (invariantSkeletonWitnessAction D sigma pi hcompat h X)
        (invariantSkeletonWitnessAction D sigma pi hcompat h Y) =
          K.toEffectiveGeometry.F X Y) := by
  have hsk : ∀ (h : H) (q r : EffectiveWitnessPart D), q ≠ r →
      s.normalized (1 : G) * (K.colour (sigma h q) (sigma h r))⁻¹ *
        (1 : G) = (K.colour q r)⁻¹ := by
    intro h q r hqr
    simp [hK h q r hqr]
  exact witnessCocycleAction_preserves_effective
    D K sigma pi hcompat (fun _ _ _ => 1)
      (by intros; rfl)
      (by intros; simp)
      hsk h

/-- For a singleton effective-colour group the skeleton invariance
requirement is AUTOMATIC; only the compatible actions on real
vertices and witness parts need to be supplied. -/
theorem invariantSkeletonWitnessAction_subsingleton_effective
    [Subsingleton G]
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (sigma : H →* Equiv.Perm (EffectiveWitnessPart D))
    (pi : H →* Equiv.Perm V)
    (hcompat : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (pi h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1))
    (h : H) :
    (∀ X Y : EffectiveWitnessVertex D,
      K.toEffectiveGeometry.part
        (invariantSkeletonWitnessAction D sigma pi hcompat h X)
        (invariantSkeletonWitnessAction D sigma pi hcompat h Y) ↔
        K.toEffectiveGeometry.part X Y) ∧
    (∀ X Y : EffectiveWitnessVertex D,
      ¬K.toEffectiveGeometry.part X Y →
      K.toEffectiveGeometry.F
        (invariantSkeletonWitnessAction D sigma pi hcompat h X)
        (invariantSkeletonWitnessAction D sigma pi hcompat h Y) =
          K.toEffectiveGeometry.F X Y) :=
  invariantSkeletonWitnessAction_preserves_effective
    D K sigma pi hcompat
    (fun _ _ _ _ => Subsingleton.elim _ _) h

end SemigenericEPPA
