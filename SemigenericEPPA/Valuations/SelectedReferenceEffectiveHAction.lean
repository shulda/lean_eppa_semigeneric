import SemigenericEPPA.Algebra.SelectedReferenceGauge
import SemigenericEPPA.Valuations.ReferenceIndexedOldSubsetLift
import SemigenericEPPA.Valuations.IndexedMultipliersWitnessHAction

/-!
# One complete relative effective H-action from selected references

For an H-action only on an induced old subset S, a homomorphic
old-label action rho and compatible quotient action iota on all
auxiliary old labels need NOT preserve ambient old cross-colours.

The selected-reference construction chooses ONE reference
z(y,j)=1 on old indices visited by S, z(y,j)=a(y,j) on S for
unvisited j, and z(y,j)=1 on unused labels. The strict index
multiplier M and this z construct ONE actual H-action on every
two-layer valuation witness vertex. The old row equations on
occupied indices and neutral multipliers on unoccupied indices
give the correct literal extension of EVERY old x in S.

If M additionally satisfies the affine skeleton equation relative
to a preselected index skeleton K0, the same action is a genuine
effective E/F-automorphism group of the fixed witness.

In particular neither full ambient F-invariance of rho nor
H-invariance of the ORIGINAL old gauge outside S is assumed.
This is the relative positive coherent effective lift interface,
with only explicit group multiplier premises remaining.
Raw-colour lifts and congruence orbit safety are separate.
-/

namespace SemigenericEPPA

universe u v w

variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- The true relative finite H-action extends every distinguished
old gauge vertex in S, and preserves E/F on the WHOLE witness,
provided the old occupied-row conditions and one fixed skeleton
equation for the index multipliers.

The skeleton K0 is chosen before S, H, rho, iota, and M; the
reference gauge z is chosen solely from S and the old coordinate
matrix a, not from H. One group homomorphism Theta is returned. -/
theorem exists_selectedReferenceEffectiveHAction
    (D : EffectiveGeometry s V)
    (S : Set V)
    (a : V → Quotient D.part → G)
    (K0 : Quotient D.part → Quotient D.part → G)
    (hReverse : ∀ i j : Quotient D.part,
      K0 j i = s (K0 i j))
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hS : ∀ (h : H) (x : V),
      x ∈ S ↔ rho h x ∈ S)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (M : H → Quotient D.part → Quotient D.part → G)
    (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
    (hMul : ∀ (k h : H) (i j : Quotient D.part),
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j)
    (hOccupiedRow : ∀ (h : H) (x : V), x ∈ S →
      ∀ j : Quotient D.part,
        (∃ y : V, y ∈ S ∧ Quotient.mk D.part y = j) →
          M h (Quotient.mk D.part x) j * a x j =
            a (rho h x) (iota h j))
    (hUnused : ∀ (h : H) (i j : Quotient D.part),
      (¬∃ y : V, y ∈ S ∧ Quotient.mk D.part y = j) →
        M h i j = 1)
    (hSkeleton : ∀ (h : H) (i j : Quotient D.part),
      s.normalized (M h i j) *
        (K0 (iota h i) (iota h j))⁻¹ *
          M h j i = (K0 i j)⁻¹) :
    ∃ Theta : H →* Equiv.Perm (EffectiveWitnessVertex D),
      (∀ (h : H) (x : V), x ∈ S →
        Theta h (D.gaugeOldWitnessVertex a x) =
          D.gaugeOldWitnessVertex a (rho h x)) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        (D.indexedWitnessSkeleton K0 hReverse).toEffectiveGeometry.part
          (Theta h X) (Theta h Y) ↔
        (D.indexedWitnessSkeleton K0 hReverse).toEffectiveGeometry.part
          X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        ¬(D.indexedWitnessSkeleton K0 hReverse).toEffectiveGeometry.part
          X Y →
        (D.indexedWitnessSkeleton K0 hReverse).toEffectiveGeometry.F
          (Theta h X) (Theta h Y) =
        (D.indexedWitnessSkeleton K0 hReverse).toEffectiveGeometry.F
          X Y) := by
  let cls : V → Quotient D.part :=
    fun x => Quotient.mk D.part x
  let z : V → Quotient D.part → G :=
    selectedReferenceGauge S cls a
  let sigma : H →* Equiv.Perm (EffectiveWitnessPart D) :=
    referenceWitnessPartAction D rho iota z
  let m : H → EffectiveWitnessPart D →
      EffectiveWitnessPart D → G :=
    fun h q r => M h q.1 r.1
  have hOneW : ∀ (q r : EffectiveWitnessPart D),
      q ≠ r → m 1 q r = 1 := by
    intro q r _
    exact hOne q.1 r.1
  have hMulW : ∀ (k h : H) (q r : EffectiveWitnessPart D),
      q ≠ r →
      m (k * h) q r =
        m k (sigma h q) (sigma h r) * m h q r := by
    intro k h q r _
    change M (k * h) q.1 r.1 =
      M k (sigma h q).1 (sigma h r).1 * M h q.1 r.1
    rw [referenceWitnessPartAction_class D rho iota z h q,
      referenceWitnessPartAction_class D rho iota z h r]
    exact hMul k h q.1 r.1
  let K : EffectiveWitnessSkeleton D :=
    D.indexedWitnessSkeleton K0 hReverse
  have hSkeletonW : ∀ (h : H) (q r : EffectiveWitnessPart D),
      q ≠ r →
      s.normalized (m h q r) *
        (K.colour (sigma h q) (sigma h r))⁻¹ *
          m h r q = (K.colour q r)⁻¹ := by
    intro h q r _
    change s.normalized (M h q.1 r.1) *
      (K0 (sigma h q).1 (sigma h r).1)⁻¹ *
        M h r.1 q.1 = (K0 q.1 r.1)⁻¹
    rw [referenceWitnessPartAction_class D rho iota z h q,
      referenceWitnessPartAction_class D rho iota z h r]
    exact hSkeleton h q.1 r.1
  have hSource : ∀ (h : H) (x : V), x ∈ S →
      ∀ y : V,
        z (rho h y) (iota h (Quotient.mk D.part x)) =
          z y (Quotient.mk D.part x) := by
    intro h x hx y
    exact selectedReferenceGauge_visited_source S cls a rho iota
      hS hcls h x y hx
  have hRow : ∀ (h : H) (x : V), x ∈ S →
      ∀ j : Quotient D.part,
        M h (Quotient.mk D.part x) j * a x j =
          a (rho h x) (iota h j) *
            referenceGaugeTwist rho iota z h x j := by
    intro h x hx j
    exact selectedReferenceGauge_old_row S cls a rho iota
      hS hcls M hOccupiedRow hUnused h x hx j
  let Theta : H →* Equiv.Perm (EffectiveWitnessVertex D) :=
    D.referenceIndexedWitnessAction rho iota z hcls
      M hOne hMul
  refine ⟨Theta, ?_, ?_, ?_⟩
  · intro h x hx
    exact D.referenceIndexedWitnessAction_maps_gaugeOld_onSubset
      S a rho iota z hcls M hOne hMul hSource hRow h x hx
  · intro h X Y
    exact (referenceWitnessCocycleAction_preserves_effective
      D K rho iota z hcls m hOneW hMulW hSkeletonW h).1 X Y
  · intro h X Y hXY
    exact (referenceWitnessCocycleAction_preserves_effective
      D K rho iota z hcls m hOneW hMulW hSkeletonW h).2 X Y hXY

end EffectiveGeometry

end SemigenericEPPA
