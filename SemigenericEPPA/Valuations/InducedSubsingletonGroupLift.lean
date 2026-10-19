import SemigenericEPPA.Valuations.PaddedSubsingletonGroupLift
import SemigenericEPPA.Valuations.OccupiedQuotientGroupAction

/-!
# Unconditional relative finite-group lift in the trivial effective sector

For G a subsingleton group, the SAME effective valuation witness over the
fixed uniform padding D.uniformPaddedGeometry supports a genuine group action
extending ANY group action on ANY induced subset S of the old carrier, provided
that action preserves the E-relation on S.

The witness carrier (and its chosen skeleton K) precedes quantification over
S, H and rho; neither the quotient-index action nor the old-label action is
an assumption. Both are produced from rho by the occupied-part construction,
then combined with the already certified padded singleton-group witness lift.

This is the unconditional H0 positive EFFECTIVE action theorem for G=1.
It is not yet an unconditional relative RAW-colour action, does not prove
the flip-safety orbit condition on cross-part raw pairs, and does not itself
assemble coherent extensions of all partial automorphisms.
-/

namespace SemigenericEPPA

universe u v w

variable {H : Type u} [Group H]
variable {G : Type v} [Group G] [Subsingleton G]
variable {V : Type w} {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- For every induced old subset S with any E-preserving H-action, the
SAME uniformly padded, two-layer effective witness admits a strict
H-action extending the prescribed action on distinguished old vertices.
The old geometry D and skeleton K are fixed independently of S and H. -/
theorem exists_inducedSubsingletonWitnessGroupLift
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D.uniformPaddedGeometry)
    (S : Set V)
    (rho : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      D.part x.val y.val ↔
        D.part (rho h x).val (rho h y).val) :
    ∃ T : H →* Equiv.Perm
        (EffectiveWitnessVertex D.uniformPaddedGeometry),
      (∀ (h : H) (x : S),
        T h (D.uniformPaddedGeometry.oldWitnessVertex
          (D.paddedOldMap x.val)) =
          D.uniformPaddedGeometry.oldWitnessVertex
            (D.paddedOldMap (rho h x).val)) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D.uniformPaddedGeometry),
        K.toEffectiveGeometry.part (T h X) (T h Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D.uniformPaddedGeometry),
        ¬K.toEffectiveGeometry.part X Y →
        K.toEffectiveGeometry.F (T h X) (T h Y) =
          K.toEffectiveGeometry.F X Y) := by
  obtain ⟨tau, iota, htau, hiota⟩ :=
    D.exists_compatibleSubsetAndQuotientActions S rho hE
  exact D.exists_paddedSubsingletonWitnessGroupLift
    K S rho tau iota htau hiota

end EffectiveGeometry

end SemigenericEPPA
