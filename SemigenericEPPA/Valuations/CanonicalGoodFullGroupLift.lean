import SemigenericEPPA.Structure.CanonicalIndexedGaugeHBridge
import SemigenericEPPA.Structure.CanonicalDiagonalGauge
import SemigenericEPPA.Algebra.OccupiedGoodDiagonalFullLaws
import SemigenericEPPA.Algebra.NormalizedDiagonalOldRowTransport
import SemigenericEPPA.Valuations.IndexedMultipliersOldVertexAction
import SemigenericEPPA.Valuations.OldEmbedding

/-!
# One canonical good effective witness and every genuine old H-action

The preceding modules separately certified: canonical quotient-indexed
old gauges; occupied H-multipliers from actual E/F-automorphisms;
their strict noncommutative cocycle and COMPLETE skeleton equations
(including old-index diagonals); the full two-layer witness H-action;
the exact old-vertex incidence transport; and normalization of the
original same-part effective dummy coordinates.

Here these are combined, without supplying auxiliary multiplier,
matrix, or diagonal transport hypotheses to the consumer.

For each original effective geometry D normalized by F=1 within E
and one good reversal-fixed raw effective colour, FIRST choose one
canonical witness skeleton K depending only on D and this colour.
For ANY compatible genuine old H-action on D, construct a strict
group homomorphism H -> Perm of the entire SAME two-layer witness.
It maps the literal old embedded vertex x to that of h x, and is an
automorphism of the witness's effective E/F geometry.

This is not yet coherent EPPA for the original raw language: the
coherent-positive proof also needs uniform safe lifts of induced
Aut(S) actions on padded replicated fibres, and a single invariant
raw-colour cover. No recentering or commutativity is assumed.
-/

namespace SemigenericEPPA

universe u v w t

variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace EffectiveGeometry

/-- One FULL witness skeleton fixed by the old effective geometry
and one genuinely good effective colour, before any H-action.
It agrees with the old gauge skeleton between distinct old E-classes
and has a reversal-fixed diagonal (the chosen good colour). -/
noncomputable def canonicalGoodWitnessSkeleton
    (D : EffectiveGeometry d.s V)
    (hGood : d.selfReverseEffective.Nonempty) :
    EffectiveWitnessSkeleton D :=
  D.indexedWitnessSkeleton
    (D.canonicalIndexedGauge.fixedGoodSkeleton hGood)
    (D.canonicalIndexedGauge.fixedGoodSkeleton_reverse_all hGood)

/-- The prechosen canonical good witness skeleton retains all old
effective cross-colours under the distinguished old embedding. -/
theorem canonicalGoodWitnessSkeleton_extendsOld
    (D : EffectiveGeometry d.s V)
    (hGood : d.selfReverseEffective.Nonempty) :
    (D.canonicalGoodWitnessSkeleton hGood).ExtendsOldSkeleton D := by
  intro i j hij
  change D.canonicalIndexedGauge.fixedGoodSkeleton hGood i j =
    D.toQuotientGauge.skeleton i j
  exact D.canonicalGoodSkeleton_extendsOld hGood i j hij

/-- Positive nontrivial-G effective group-lift theorem for an ACTUAL
full old H-action. A single skeleton is chosen before rho, iota, or H.
Every group element acts on the same two-layer valuation witness,
preserves/refects E and every effective cross-colour, and acts on
distinguished old vertices LITERALLY as rho.

All multiplier existence, strict cocycle, reverse/skeleton equations,
and exact old-row transport are established from the canonical indexed
presentation: none is an additional consumer hypothesis.

The only geometric assumptions are the genuine old H-automorphism
laws and the standard normalization of same-part dummy effective
values to 1. (The original R1--R3 effective presentation has the
latter automatically.)
-/
theorem exists_canonicalGoodWitnessGroupAction
    (D : EffectiveGeometry d.s V)
    (hGood : d.selfReverseEffective.Nonempty)
    (hSame : ∀ x y : V, D.part x y → D.F x y = 1)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (hE : ∀ (h : H) (x y : V),
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ (h : H) (x y : V), ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y) :
    ∃ Theta : H →* Equiv.Perm (EffectiveWitnessVertex D),
      (∀ (h : H) (x : V),
        Theta h (D.oldWitnessVertex x) =
          D.oldWitnessVertex (rho h x)) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        (D.canonicalGoodWitnessSkeleton hGood).toEffectiveGeometry.part
          (Theta h X) (Theta h Y) ↔
        (D.canonicalGoodWitnessSkeleton hGood).toEffectiveGeometry.part
          X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        ¬(D.canonicalGoodWitnessSkeleton hGood).toEffectiveGeometry.part X Y →
        (D.canonicalGoodWitnessSkeleton hGood).toEffectiveGeometry.F
          (Theta h X) (Theta h Y) =
        (D.canonicalGoodWitnessSkeleton hGood).toEffectiveGeometry.F
          X Y) := by
  let P : IndexedGauge d.s V (Quotient D.part) :=
    D.canonicalIndexedGauge
  have hLabel : ∀ (h : H) (x : V),
      P.label (rho h x) = iota h (P.label x) :=
    D.canonicalIndexedGauge_H_labels rho iota hcls
  have hEffective : ∀ (h : H) (x y : V),
      ¬P.toEffectiveGeometry.part x y →
        P.toEffectiveGeometry.F (rho h x) (rho h y) =
        P.toEffectiveGeometry.F x y :=
    D.canonicalIndexedGauge_H_invariant rho hE hF
  let M : H → Quotient D.part → Quotient D.part → G :=
    P.oldActionMultipliers rho iota
  obtain ⟨hMone, hMmul⟩ :=
    P.oldActionMultipliers_group_laws rho iota hLabel hEffective
  have hDiag : ∀ x : V, P.vertexGauge x (P.label x) = 1 := by
    intro x
    change D.toQuotientGauge.vertexGauge x
      (Quotient.mk D.part x) = 1
    exact D.quotientGauge_diagonal_one hSame x
  have hRow : ∀ (h : H) (x : V) (j : Quotient D.part),
      M h (Quotient.mk D.part x) j *
        D.toQuotientGauge.vertexGauge x j =
          D.toQuotientGauge.vertexGauge (rho h x) (iota h j) := by
    intro h x j
    have hj : P.occupied j := D.canonicalIndexedGauge_occupied j
    have hR := P.oldActionMultipliers_transport_all_occupied
      rho iota hLabel hEffective hDiag h x j hj
    exact hR
  let K : EffectiveWitnessSkeleton D :=
    D.canonicalGoodWitnessSkeleton hGood
  let z : V → Quotient D.part → G := fun _ _ => 1
  let m : H → EffectiveWitnessPart D →
      EffectiveWitnessPart D → G :=
    fun h q r => M h q.1 r.1
  have hOneWitness : ∀ (q r : EffectiveWitnessPart D),
      q ≠ r → m 1 q r = 1 := by
    intro q r _
    exact hMone q.1 r.1
  have hMulWitness : ∀ (k h : H)
      (q r : EffectiveWitnessPart D), q ≠ r →
      m (k * h) q r =
        m k (referenceWitnessPartAction D rho iota z h q)
          (referenceWitnessPartAction D rho iota z h r) *
          m h q r := by
    intro k h q r _
    change M (k * h) q.1 r.1 =
      M k (referenceWitnessPartAction D rho iota z h q).1
        (referenceWitnessPartAction D rho iota z h r).1 *
      M h q.1 r.1
    rw [referenceWitnessPartAction_class D rho iota z h q,
      referenceWitnessPartAction_class D rho iota z h r]
    exact hMmul k h q.1 r.1
  have hSkeletonWitness : ∀ (h : H)
      (q r : EffectiveWitnessPart D), q ≠ r →
      d.s.normalized (m h q r) *
        (K.colour (referenceWitnessPartAction D rho iota z h q)
          (referenceWitnessPartAction D rho iota z h r))⁻¹ *
        m h r q = (K.colour q r)⁻¹ := by
    intro h q r _
    change d.s.normalized (M h q.1 r.1) *
      (P.fixedGoodSkeleton hGood
        (referenceWitnessPartAction D rho iota z h q).1
        (referenceWitnessPartAction D rho iota z h r).1)⁻¹ *
      M h r.1 q.1 = (P.fixedGoodSkeleton hGood q.1 r.1)⁻¹
    rw [referenceWitnessPartAction_class D rho iota z h q,
      referenceWitnessPartAction_class D rho iota z h r]
    exact P.fixedGoodSkeleton_preserved_all hGood
      rho iota hLabel hEffective h q.1 r.1
  let Theta : H →* Equiv.Perm (EffectiveWitnessVertex D) :=
    D.indexedWitnessAction rho iota hcls M hMone hMmul
  refine ⟨Theta, ?_, ?_, ?_⟩
  · intro h x
    exact D.indexedWitnessAction_maps_old
      rho iota hcls M hMone hMmul hRow h x
  · intro h X Y
    exact (referenceWitnessCocycleAction_preserves_effective
      D K rho iota z hcls m hOneWitness hMulWitness
      hSkeletonWitness h).1 X Y
  · intro h X Y hXY
    exact (referenceWitnessCocycleAction_preserves_effective
      D K rho iota z hcls m hOneWitness hMulWitness
      hSkeletonWitness h).2 X Y hXY

end EffectiveGeometry

end SemigenericEPPA
