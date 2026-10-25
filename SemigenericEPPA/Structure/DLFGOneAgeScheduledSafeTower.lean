import SemigenericEPPA.Structure.DLFGOneSafePairAgeJointSuccessorWithConnectors
import SemigenericEPPA.Structure.DLFSafePairTowerAgeSchedule

/-!
# G=1: countable age-scheduled safe-pair tower without any good orbit

The exceptional G=1 age-target connector successor proves exactly the
same stage specification as the complete-good-orbit finite step,
without imposing HasCompleteGoodOrbit. We reuse the original
FiniteRawAgeTarget and HasTargetConnectorSuccessor APIs and perform
classical recursive choice of actual finite safe-pair states.

The resulting full finite tower has strict H-actions, extends every
old original E/R_c partial automorphism at the very next stage,
and embeds every prescribed finite raw age target on schedule.
This is a tower existence result; homogeneity, full age and dense
locally finite automorphisms are handled by the existing
downstream limit modules.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

namespace FiniteSafePairState

/-- G=1 supplies each age target and all old connectors in one successor. -/
theorem exists_gOne_targetConnectorSuccessor
    (A : FiniteSafePairState d)
    (Q : FiniteRawAgeTarget d) :
    ∃ B : FiniteSafePairState d, A.HasTargetConnectorSuccessor B Q := by
  classical
  letI : Finite A.carrier := A.finite_carrier
  letI : Fintype A.carrier := Fintype.ofFinite A.carrier
  letI : Finite Q.carrier := Q.finite_carrier
  letI : Fintype Q.carrier := Fintype.ofFinite Q.carrier
  obtain ⟨W, hW, B, f, q, hqInj, hqPart, hqColour, hOld⟩ :=
    A.pair.exists_gOneSafeExtension_containingFiniteRaw_withConnectors
      Q.raw
  letI : Finite W := hW
  let newState : FiniteSafePairState d := {
    carrier := W
    finite_carrier := hW
    pair := B
  }
  exact ⟨newState, f, q, hqInj, hqPart, hqColour, hOld⟩

private noncomputable def gOneAgeNext
    (A : FiniteSafePairState d)
    (Q : FiniteRawAgeTarget d) : FiniteSafePairState d :=
  Classical.choose (A.exists_gOne_targetConnectorSuccessor Q)

private theorem gOneAgeNext_spec
    (A : FiniteSafePairState d)
    (Q : FiniteRawAgeTarget d) :
    A.HasTargetConnectorSuccessor (gOneAgeNext A Q) Q :=
  Classical.choose_spec (A.exists_gOne_targetConnectorSuccessor Q)

private noncomputable def gOneAgeSeq
    (A₀ : FiniteSafePairState d)
    (targets : ℕ → FiniteRawAgeTarget d) :
    ℕ → FiniteSafePairState d
  | 0 => A₀
  | n + 1 => gOneAgeNext (gOneAgeSeq A₀ targets n) (targets n)

private theorem gOneAgeSeq_step
    (A₀ : FiniteSafePairState d)
    (targets : ℕ → FiniteRawAgeTarget d)
    (n : ℕ) :
    HasTargetConnectorSuccessor
      (gOneAgeSeq A₀ targets n)
      (gOneAgeSeq A₀ targets (n + 1))
      (targets n) :=
  gOneAgeNext_spec (gOneAgeSeq A₀ targets n) (targets n)

end FiniteSafePairState

/-- Exceptional G=1: genuine safe tower realizing an arbitrary finite
raw age schedule, with all next-stage old partial connectors. -/
theorem exists_gOne_safeTower_realizingAgeSchedule
    (A₀ : FiniteSafePairState d)
    (targets : ℕ → FiniteRawAgeTarget d) :
    ∃ (V : ℕ → Type (max u v))
      (hV : ∀ n, Finite (V n)),
      letI : ∀ n, Finite (V n) := hV
      ∃ T : FiniteSafeRawPairTower d V,
        T.HasNextStageRawConnectors ∧
        V 0 = A₀.carrier ∧
        (∀ n : ℕ, ∃ q : (targets n).carrier → V (n+1),
          Function.Injective q ∧
          (∀ x y : (targets n).carrier,
            (T.stage (n+1)).raw.part (q x) (q y) ↔
              (targets n).raw.part x y) ∧
          (∀ x y : (targets n).carrier,
            (T.stage (n+1)).raw.colour (q x) (q y) =
              (targets n).raw.colour x y)) := by
  classical
  let states : ℕ → FiniteSafePairState d :=
    FiniteSafePairState.gOneAgeSeq A₀ targets
  have hSucc (n : ℕ) :
      FiniteSafePairState.HasTargetConnectorSuccessor
        (states n) (states (n+1)) (targets n) :=
    FiniteSafePairState.gOneAgeSeq_step A₀ targets n
  let V : ℕ → Type (max u v) := fun n => (states n).carrier
  let hV : ∀ n, Finite (V n) := fun n => (states n).finite_carrier
  letI : ∀ n, Finite (V n) := hV
  let T : FiniteSafeRawPairTower d V := {
    stage := fun n => (states n).pair
    step := fun n => Classical.choose (hSucc n)
  }
  have hStep (n : ℕ) (x : V n) :
      T.vertexTransition n (n+1) (Nat.le_succ n) x =
        (T.step n).vertex x := by
    change (T.between n (n+1) (Nat.le_succ n)).vertex x =
      (T.step n).vertex x
    rw [T.between_succ_vertex n n le_rfl x,
      T.between_self_vertex n x]
  refine ⟨V, hV, T, ?_, ?_, ?_⟩
  · intro n S p hp hPart hColour
    obtain ⟨q, _hqInj, _hqPart, _hqColour, hPartials⟩ :=
      Classical.choose_spec (hSucc n)
    obtain ⟨k, hk⟩ := hPartials S p hp hPart hColour
    refine ⟨k, ?_⟩
    intro x
    change k.val.val
      ((T.vertexTransition n (n+1) (Nat.le_succ n)) x.val) =
      (T.vertexTransition n (n+1) (Nat.le_succ n)) (p x)
    rw [hStep n x.val, hStep n (p x)]
    exact hk x
  · rfl
  · intro n
    obtain ⟨q, hInj, hPart, hColour, _hOld⟩ :=
      Classical.choose_spec (hSucc n)
    exact ⟨q, hInj, hPart, hColour⟩

end SemigenericEPPA
