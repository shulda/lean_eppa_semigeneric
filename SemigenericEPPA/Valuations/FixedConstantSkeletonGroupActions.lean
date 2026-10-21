import SemigenericEPPA.Valuations.FixedSkeletonExtensionality
import Mathlib.Algebra.Group.End

/-!
# Move the good witness skeleton outside every selected H-action

The positive coherent EPPA proof has the quantifier order

  ∃ (fixed witness B) (fixed skeleton K) (fixed old embedding),
      ∀ (selected induced S) (group H) (rho:H→Aut S),
        ∃ (strict extension Theta:H→Aut B), ...

Several already-certified group-lift theorems are written with
  ∃ K Theta, constant(K,g0) ∧ ...
under a later choice of S and H. Skeleton extensionality shows
that the dependence on S/H here is illusory: a witness skeleton
is uniquely determined by its colour matrix, and the returned
matrix is always the single constant g0 chosen earlier.

This theorem packages the exact transport of a strict action from
its existentially returned constant-g0 skeleton to ANY previously
fixed constant-g0 skeleton. It also transports the complete E/F
automorphism laws and arbitrary other predicates on Theta (such
as literal extension of a fixed old zero-section).

The result is not just "isomorphic" skeletons: it is literal
equality in Lean, including the proof-valued reversal field via
proof irrelevance. Hence no new witness, embedding, or action is
chosen and all group laws remain exactly as before.

This bridges the quantifier-order gap of the fixed factorial
relative effective H-action (#293). Raw cover and coherent
groupoid assembly remain independent gates.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {V : Type v}
variable {H : Type w} [Group H]
variable {s : AffineAntiInvolution G}

/-- Once a constant-good skeleton K0 is chosen, ANY later
existential effective group action on a constant-good skeleton
can be moved to that SAME K0. The strict group homomorphism
Theta is not modified, nor are any old-copy extension conditions
expressed by the predicate P. -/
theorem EffectiveWitnessSkeleton.exists_action_on_preselected_constant
    (D : EffectiveGeometry s V)
    (K0 : EffectiveWitnessSkeleton D)
    (g0 : G)
    (hK0 : ∀ q r : EffectiveWitnessPart D,
      K0.colour q r = g0)
    (P : (H →* Equiv.Perm (EffectiveWitnessVertex D)) → Prop)
    (hExists :
      ∃ (K : EffectiveWitnessSkeleton D)
        (Theta : H →* Equiv.Perm (EffectiveWitnessVertex D)),
        (∀ q r : EffectiveWitnessPart D, K.colour q r = g0) ∧
        P Theta ∧
        (∀ (h : H) (X Y : EffectiveWitnessVertex D),
          K.toEffectiveGeometry.part (Theta h X) (Theta h Y) ↔
            K.toEffectiveGeometry.part X Y) ∧
        (∀ (h : H) (X Y : EffectiveWitnessVertex D),
          ¬K.toEffectiveGeometry.part X Y →
          K.toEffectiveGeometry.F (Theta h X) (Theta h Y) =
            K.toEffectiveGeometry.F X Y)) :
    ∃ Theta : H →* Equiv.Perm (EffectiveWitnessVertex D),
      P Theta ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        K0.toEffectiveGeometry.part (Theta h X) (Theta h Y) ↔
          K0.toEffectiveGeometry.part X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        ¬K0.toEffectiveGeometry.part X Y →
        K0.toEffectiveGeometry.F (Theta h X) (Theta h Y) =
          K0.toEffectiveGeometry.F X Y) := by
  obtain ⟨K, Theta, hK, hP, hE, hF⟩ := hExists
  have hEqual : K = K0 := K.eq_of_sameConstant K0 g0 hK hK0
  subst K
  exact ⟨Theta, hP, hE, hF⟩

end SemigenericEPPA
