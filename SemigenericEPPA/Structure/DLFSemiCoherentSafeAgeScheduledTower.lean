import SemigenericEPPA.Structure.DLFSemiCoherentSafeAgeTargetSuccessor
import SemigenericEPPA.Structure.DLFSafePairTowerAgeSchedule

/-!
# An actual age-cofinal raw safe-pair tower from the finite family condition

If every finite safe raw group-action pair extends strictly over
every prescribed finite age superstructure while realizing all
its partial original raw automorphisms, one can build an actual
countable chain of finite safe pairs meeting an arbitrary schedule
of original E/Option-C finite age targets.

The step theorem uses precisely the conditional finite successor;
the remainder is the already Lean-certified direct finite-stage
tower recursion, all connectors and exact induced scheduled ages.
No complete good orbit or subsingleton G hypothesis is used
in this implication. Thus the class's concrete finite
semi-coherent group-extension family has an explicit DLF
limit construction, independent of Sagi's general equivalence.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

namespace FiniteSafePairState

/-- The cofinal safe finite-action property supplies a successor meeting every target. -/
theorem exists_safeFamily_targetConnectorSuccessor
    (A : FiniteSafePairState d)
    (Q : FiniteRawAgeTarget d)
    (hCofinal : d.HasCofinalSafeFiniteGroupExtension) :
    ∃ B : FiniteSafePairState d, A.HasTargetConnectorSuccessor B Q := by
  classical
  letI : Finite A.carrier := A.finite_carrier
  letI : Fintype A.carrier := Fintype.ofFinite A.carrier
  letI : Finite Q.carrier := Q.finite_carrier
  letI : Fintype Q.carrier := Fintype.ofFinite Q.carrier
  obtain ⟨W, hW, B, f, q, hqInj, hqPart, hqColour, hOld⟩ :=
    A.pair.exists_safeExtension_containingRaw_of_cofinalSafe
      Q.raw hCofinal
  letI : Finite W := hW
  let newState : FiniteSafePairState d := {
    carrier := W
    finite_carrier := hW
    pair := B
  }
  exact ⟨newState, f, q, hqInj, hqPart, hqColour, hOld⟩

private noncomputable def safeFamilyAgeNext
    (hCofinal : d.HasCofinalSafeFiniteGroupExtension)
    (A : FiniteSafePairState d)
    (Q : FiniteRawAgeTarget d) : FiniteSafePairState d :=
  Classical.choose (A.exists_safeFamily_targetConnectorSuccessor Q hCofinal)

private theorem safeFamilyAgeNext_spec
    (hCofinal : d.HasCofinalSafeFiniteGroupExtension)
    (A : FiniteSafePairState d)
    (Q : FiniteRawAgeTarget d) :
    A.HasTargetConnectorSuccessor (safeFamilyAgeNext hCofinal A Q) Q :=
  Classical.choose_spec (A.exists_safeFamily_targetConnectorSuccessor Q hCofinal)

private noncomputable def safeFamilyAgeSeq
    (hCofinal : d.HasCofinalSafeFiniteGroupExtension)
    (A₀ : FiniteSafePairState d)
    (targets : ℕ → FiniteRawAgeTarget d) :
    ℕ → FiniteSafePairState d
  | 0 => A₀
  | n + 1 => safeFamilyAgeNext hCofinal (safeFamilyAgeSeq hCofinal A₀ targets n) (targets n)

private theorem safeFamilyAgeSeq_step
    (hCofinal : d.HasCofinalSafeFiniteGroupExtension)
    (A₀ : FiniteSafePairState d)
    (targets : ℕ → FiniteRawAgeTarget d)
    (n : ℕ) :
    HasTargetConnectorSuccessor
      (safeFamilyAgeSeq hCofinal A₀ targets n)
      (safeFamilyAgeSeq hCofinal A₀ targets (n + 1))
      (targets n) :=
  safeFamilyAgeNext_spec hCofinal (safeFamilyAgeSeq hCofinal A₀ targets n) (targets n)

end FiniteSafePairState

/-- Conditional genuine safe tower realizing an arbitrary finite raw age schedule with all next-stage old partial connectors. -/
theorem exists_safeFamily_safeTower_realizingAgeSchedule
    (hCofinal : d.HasCofinalSafeFiniteGroupExtension)
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
    FiniteSafePairState.safeFamilyAgeSeq hCofinal A₀ targets
  have hSucc (n : ℕ) :
      FiniteSafePairState.HasTargetConnectorSuccessor
        (states n) (states (n+1)) (targets n) :=
    FiniteSafePairState.safeFamilyAgeSeq_step hCofinal A₀ targets n
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
