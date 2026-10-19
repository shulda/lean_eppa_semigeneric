import SemigenericEPPA.Valuations.EffectiveEPPA
import SemigenericEPPA.Valuations.InducedSubsingletonGroupLift

/-!
# One fixed finite G=1 effective EPPA witness with all relative group lifts

The ordinary effective EPPA theorem provides an induced old embedding
into ONE finite valuation witness that extends all individual partial
automorphisms.

For a subsingleton effective group G, the SAME witness additionally
admits a strict group action extending the automorphisms of EVERY
induced old substructure S, not merely one arbitrarily fixed S.
The witness, old embedding and skeleton are chosen before quantifying
over S or its group H.

This precise combined interface is the positive G=1 EFFECTIVE gate
for the coherent program.  It is weaker than coherent raw-colour EPPA:
it neither supplies a safe action on raw-colour fibres nor the final
coherent groupoid assignment.
-/

namespace SemigenericEPPA

universe u v t

variable {G : Type u} [Group G] [Subsingleton G]
variable {V : Type v} {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- A single finite induced effective witness simultaneously has
ordinary EPPA and homomorphic H-extensions for EVERY later induced
subset S with EVERY E-preserving H-action on that subset, when G=1.
All quantifiers over H and S occur after the existential skeleton. -/
theorem finite_subsingletonEffectiveEPPA_and_allGroupLifts
    [Finite V] [Finite G] (D : EffectiveGeometry s V) :
    Finite (EffectiveWitnessVertex D.uniformPaddedGeometry) ∧
    ∃ K : EffectiveWitnessSkeleton D.uniformPaddedGeometry,
      K.ExtendsOldSkeleton D.uniformPaddedGeometry ∧
      Function.Injective
        (fun x : V =>
          D.uniformPaddedGeometry.oldWitnessVertex
            (D.paddedOldMap x)) ∧
      (∀ x y : V,
        K.toEffectiveGeometry.part
          (D.uniformPaddedGeometry.oldWitnessVertex (D.paddedOldMap x))
          (D.uniformPaddedGeometry.oldWitnessVertex (D.paddedOldMap y)) ↔
            D.part x y) ∧
      (∀ x y : V, ¬D.part x y →
        K.toEffectiveGeometry.F
          (D.uniformPaddedGeometry.oldWitnessVertex (D.paddedOldMap x))
          (D.uniformPaddedGeometry.oldWitnessVertex (D.paddedOldMap y)) =
            D.F x y) ∧
      (∀ (S : Set V) (p : S → V),
        Function.Injective p →
        (∀ x y : S, D.part x.val y.val ↔ D.part (p x) (p y)) →
        (∀ x y : S, ¬D.part x.val y.val →
          D.F (p x) (p y) = D.F x.val y.val) →
        ∃ T : EffectiveWitnessVertex D.uniformPaddedGeometry ≃
            EffectiveWitnessVertex D.uniformPaddedGeometry,
          (∀ x : S,
            T (D.uniformPaddedGeometry.oldWitnessVertex
                (D.paddedOldMap x.val)) =
              D.uniformPaddedGeometry.oldWitnessVertex
                (D.paddedOldMap (p x))) ∧
          (∀ X Y : EffectiveWitnessVertex D.uniformPaddedGeometry,
            K.toEffectiveGeometry.part (T X) (T Y) ↔
              K.toEffectiveGeometry.part X Y) ∧
          (∀ X Y : EffectiveWitnessVertex D.uniformPaddedGeometry,
            ¬K.toEffectiveGeometry.part X Y →
              K.toEffectiveGeometry.F (T X) (T Y) =
                K.toEffectiveGeometry.F X Y)) ∧
      (∀ (H : Type t) [Group H]
          (S : Set V) (rho : H →* Equiv.Perm S),
        (∀ (h : H) (x y : S),
          D.part x.val y.val ↔
            D.part (rho h x).val (rho h y).val) →
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
                K.toEffectiveGeometry.F X Y)) := by
  obtain ⟨hf, K, hK, hinj, hPart, hColour, hEPPA⟩ :=
    D.finite_effectiveEPPA_witness
  refine ⟨hf, K, hK, hinj, hPart, hColour, hEPPA, ?_⟩
  intro H _ S rho hE
  exact D.exists_inducedSubsingletonWitnessGroupLift K S rho hE

end EffectiveGeometry

end SemigenericEPPA
