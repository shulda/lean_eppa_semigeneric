import SemigenericEPPA.Valuations.ReferenceWitnessActionBridge

/-!
# From index-pair multipliers to a real full witness H-action

The positive nontrivial-G construction produces multipliers M_h(i,j)
on the ORIGINAL E-class indices I=V/E, not independently on all
pairs q=(i,f), r=(j,g) of blown-up witness parts.

The existing WitnessCocycleAction interface requires pair multipliers
for every q,r. Pull back the SAME M_h(i,j) along the first coordinate
of each witness part, and pull back ONE fixed index skeleton K(i,j).

The subtle point is that different witness parts can have the SAME
first index i: the old index skeleton must therefore satisfy reversal
also on K(i,i), rather than only on distinct old indices. A genuinely
s-fixed good default, as constructed for the occupied skeleton,
provides exactly this extra diagonal property.

The result is one actual group homomorphism H -> Perm of the COMPLETE
two-layer valuation carrier, preserving E and every effective colour.
The old-label and class-index transports are literal. This is an
algebraic/witness-action assembly given the index-level equations,
not yet the proof that suitable multipliers exist simultaneously
for every induced old subgroup or that the raw-cover lift is safe.
-/

namespace SemigenericEPPA

universe u v w

variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- Pull back a reversible skeleton on the old quotient indices
to ALL blown-up witness parts. Reversal is needed also on the old
index diagonal, since two different witness parts may share it. -/
def indexedWitnessSkeleton
    (D : EffectiveGeometry s V)
    (K₀ : Quotient D.part → Quotient D.part → G)
    (hReverse : ∀ i j : Quotient D.part,
      K₀ j i = s (K₀ i j)) :
    EffectiveWitnessSkeleton D where
  colour := fun q r => K₀ q.1 r.1
  reverse := by
    intro q r _
    exact hReverse q.1 r.1

/-- A strict index-level cocycle M_h(i,j) and one fixed indexed
skeleton satisfying the affine compatibility identity on EVERY
ordered index pair give a real H-action on the full valuation
witness. No separate witness-part multiplier choices occur.

The action extends the prescribed old real-label and part-index
permutations. Literal old-vertex embedding compatibility and
raw-colour flip safety are subsequent, distinct gates. -/
theorem exists_indexedWitnessHAction
    (D : EffectiveGeometry s V)
    (K₀ : Quotient D.part → Quotient D.part → G)
    (hReverse : ∀ i j : Quotient D.part,
      K₀ j i = s (K₀ i j))
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (M : H → Quotient D.part → Quotient D.part → G)
    (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
    (hMul : ∀ (k h : H) (i j : Quotient D.part),
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j)
    (hSkeleton : ∀ (h : H) (i j : Quotient D.part),
      s.normalized (M h i j) *
        (K₀ (iota h i) (iota h j))⁻¹ *
          M h j i = (K₀ i j)⁻¹) :
    ∃ (K : EffectiveWitnessSkeleton D)
        (Theta : H →* Equiv.Perm (EffectiveWitnessVertex D)),
      (∀ q r : EffectiveWitnessPart D,
        K.colour q r = K₀ q.1 r.1) ∧
      (∀ (h : H) (X : EffectiveWitnessVertex D),
        (Theta h X).part.1 = iota h X.part.1) ∧
      (∀ (h : H) (X : EffectiveWitnessVertex D),
        (Theta h X).old = rho h X.old) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        K.toEffectiveGeometry.part (Theta h X) (Theta h Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        ¬K.toEffectiveGeometry.part X Y →
        K.toEffectiveGeometry.F (Theta h X) (Theta h Y) =
          K.toEffectiveGeometry.F X Y) := by
  let K : EffectiveWitnessSkeleton D :=
    D.indexedWitnessSkeleton K₀ hReverse
  let sigma : H →* Equiv.Perm (EffectiveWitnessPart D) :=
    referenceWitnessPartAction D rho iota z
  let m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G :=
    fun h q r => M h q.1 r.1
  have hmOne :
      ∀ q r : EffectiveWitnessPart D, q ≠ r → m 1 q r = 1 := by
    intro q r _
    exact hOne q.1 r.1
  have hmMul :
      ∀ (k h : H) (q r : EffectiveWitnessPart D), q ≠ r →
        m (k * h) q r = m k (sigma h q) (sigma h r) * m h q r := by
    intro k h q r _
    change M (k * h) q.1 r.1 =
      M k (sigma h q).1 (sigma h r).1 * M h q.1 r.1
    rw [referenceWitnessPartAction_class D rho iota z h q,
      referenceWitnessPartAction_class D rho iota z h r]
    exact hMul k h q.1 r.1
  have hmSkeleton :
      ∀ (h : H) (q r : EffectiveWitnessPart D), q ≠ r →
        s.normalized (m h q r) *
          (K.colour (sigma h q) (sigma h r))⁻¹ *
            m h r q = (K.colour q r)⁻¹ := by
    intro h q r _
    change s.normalized (M h q.1 r.1) *
      (K₀ (sigma h q).1 (sigma h r).1)⁻¹ *
        M h r.1 q.1 = (K₀ q.1 r.1)⁻¹
    rw [referenceWitnessPartAction_class D rho iota z h q,
      referenceWitnessPartAction_class D rho iota z h r]
    exact hSkeleton h q.1 r.1
  let Theta : H →* Equiv.Perm (EffectiveWitnessVertex D) :=
    referenceWitnessCocycleAction D rho iota z hcls
      m hmOne hmMul
  refine ⟨K, Theta, ?_, ?_, ?_, ?_, ?_⟩
  · intro q r
    rfl
  · intro h X
    change (witnessCocyclePerm D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X).part.1 = iota h X.part.1
    rw [witnessCocyclePerm_part]
    exact referenceWitnessPartAction_class D rho iota z h X.part
  · intro h X
    change (witnessCocyclePerm D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X).old = rho h X.old
    exact witnessCocyclePerm_old D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X
  · intro h X Y
    exact (referenceWitnessCocycleAction_preserves_effective
      D K rho iota z hcls m hmOne hmMul hmSkeleton h).1 X Y
  · intro h X Y hXY
    exact (referenceWitnessCocycleAction_preserves_effective
      D K rho iota z hcls m hmOne hmMul hmSkeleton h).2 X Y hXY

end EffectiveGeometry

end SemigenericEPPA
