import SemigenericEPPA.Structure.DLFSafePairTowerExistence
import SemigenericEPPA.Structure.DLFSafePairAgeJointSuccessorWithConnectors
import SemigenericEPPA.Structure.DLFSafePairTowerLimitRawRectangle

/-!
# A countable safe-pair tower with ALL connectors and ANY prescribed age schedule

The finite age-target successor theorem permits one to demand TWO
features at every new finite stage, simultaneously:
(1) all original partial automorphisms of the old stage extend
    inside the new finite safe automorphism subgroup, and
(2) an arbitrary scheduled finite original E/R_c rectangle embeds
    inducedly in the new structure.

We package both requirements into one successor relation on finite
safe pairs with carrier types in one fixed universe. Classical choice
and primitive recursion construct an ACTUAL ℕ-indexed tower satisfying
both. There is no homogeneity assumption on the scheduled targets.

Every scheduled finite target then embeds literally in the original
infinite R1–R3 quotient-limit rectangle by the canonical stage map.

An enumeration of representatives for ALL isomorphism types of
finite raw rectangles will provide AGE COFINALITY. This module
allows any prescribed enumeration; it does not yet establish such
an enumeration exists or identify the limit with a Fraïssé limit.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

/-- A finite original-language raw rectangle, with its finite
carrier packed in the canonical common universe of G and C. -/
structure FiniteRawAgeTarget (d : RawDatum G C) where
  carrier : Type (max u v)
  finite_carrier : Finite carrier
  raw : RawRectanglePresentation d carrier

namespace FiniteSafePairState

/-- One genuine age-scheduled successor of finite safe raw pairs:
a STRICT equivariant safe-pair embedding, an exact induced copy of
the prescribed target, and EVERY original partial connector on
the same next-stage finite safe group. -/
def HasTargetConnectorSuccessor
    (A B : FiniteSafePairState d)
    (Q : FiniteRawAgeTarget d) : Prop :=
  letI : Finite A.carrier := A.finite_carrier
  letI : Finite B.carrier := B.finite_carrier
  ∃ (f : FiniteSafeRawPairEmbedding A.pair B.pair)
    (q : Q.carrier → B.carrier),
    Function.Injective q ∧
    (∀ x y : Q.carrier, B.pair.raw.part (q x) (q y) ↔ Q.raw.part x y) ∧
    (∀ x y : Q.carrier, B.pair.raw.colour (q x) (q y) = Q.raw.colour x y) ∧
    (∀ (S : Set A.carrier) (p : S → A.carrier),
      Function.Injective p →
      (∀ x y : S, A.pair.raw.part x.val y.val ↔
        A.pair.raw.part (p x) (p y)) →
      (∀ x y : S, A.pair.raw.colour (p x) (p y) =
        A.pair.raw.colour x.val y.val) →
      ∃ k : B.pair.subgroup,
        ∀ x : S, k.val.val (f.vertex x.val) = f.vertex (p x))

/-- One complete affine good orbit supplies a successor meeting an
ARBITRARY prescribed finite age target AND all old connectors. -/
theorem exists_targetConnectorSuccessor
    (A : FiniteSafePairState d)
    (Q : FiniteRawAgeTarget d)
    (hOrbit : d.HasCompleteGoodOrbit) :
    ∃ B : FiniteSafePairState d, A.HasTargetConnectorSuccessor B Q := by
  classical
  letI : Finite A.carrier := A.finite_carrier
  letI : Fintype A.carrier := Fintype.ofFinite A.carrier
  letI : Fintype Q.carrier := Fintype.ofFinite Q.carrier
  obtain ⟨W, hW, B, f, q, hqInj, hqPart, hqColour, hOld⟩ :=
    A.pair.exists_safeExtension_containingFiniteRaw_withConnectors
      Q.raw hOrbit
  letI : Finite W := hW
  let newState : FiniteSafePairState d := {
    carrier := W
    finite_carrier := hW
    pair := B
  }
  exact ⟨newState, f, q, hqInj, hqPart, hqColour, hOld⟩

private noncomputable def ageNext
    (hOrbit : d.HasCompleteGoodOrbit)
    (A : FiniteSafePairState d)
    (Q : FiniteRawAgeTarget d) : FiniteSafePairState d :=
  Classical.choose (A.exists_targetConnectorSuccessor Q hOrbit)

private theorem ageNext_spec
    (hOrbit : d.HasCompleteGoodOrbit)
    (A : FiniteSafePairState d)
    (Q : FiniteRawAgeTarget d) :
    A.HasTargetConnectorSuccessor (ageNext hOrbit A Q) Q :=
  Classical.choose_spec (A.exists_targetConnectorSuccessor Q hOrbit)

private noncomputable def ageSeq
    (hOrbit : d.HasCompleteGoodOrbit)
    (A₀ : FiniteSafePairState d)
    (targets : ℕ → FiniteRawAgeTarget d) :
    ℕ → FiniteSafePairState d
  | 0 => A₀
  | n + 1 => ageNext hOrbit (ageSeq hOrbit A₀ targets n) (targets n)

private theorem ageSeq_step
    (hOrbit : d.HasCompleteGoodOrbit)
    (A₀ : FiniteSafePairState d)
    (targets : ℕ → FiniteRawAgeTarget d)
    (n : ℕ) :
    HasTargetConnectorSuccessor
      (ageSeq hOrbit A₀ targets n)
      (ageSeq hOrbit A₀ targets (n + 1))
      (targets n) :=
  ageNext_spec hOrbit (ageSeq hOrbit A₀ targets n) (targets n)

end FiniteSafePairState

/-- An ACTUAL countable tower of finite safe original-language
rectangles extending EVERY old partial automorphism at the NEXT
stage, and containing each prescribed finite age target Q_n at
stage n+1 as an induced exact E/R_c substructure.

The initial finite safe pair A₀ is arbitrary. No prior existence
of a tower, coherence on all of A⊕Q, or SAP is assumed. -/
theorem exists_safeTower_realizingAgeSchedule
    (A₀ : FiniteSafePairState d)
    (targets : ℕ → FiniteRawAgeTarget d)
    (hOrbit : d.HasCompleteGoodOrbit) :
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
    FiniteSafePairState.ageSeq hOrbit A₀ targets
  have hSucc (n : ℕ) :
      FiniteSafePairState.HasTargetConnectorSuccessor
        (states n) (states (n+1)) (targets n) :=
    FiniteSafePairState.ageSeq_step hOrbit A₀ targets n
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

/-- If every prescribed finite target Q_n occurs in stage n+1,
then each Q_n embeds inducedly into the actual infinite quotient
limit, with literal original E and every ordered raw colour. -/
theorem safeTower_ageSchedule_embedsInLimit
    {V : ℕ → Type (max u v)}
    [∀ n, Finite (V n)]
    (T : FiniteSafeRawPairTower d V)
    (targets : ℕ → FiniteRawAgeTarget d)
    (hTargets : ∀ n : ℕ, ∃ q : (targets n).carrier → V (n+1),
      Function.Injective q ∧
      (∀ x y : (targets n).carrier,
        (T.stage (n+1)).raw.part (q x) (q y) ↔ (targets n).raw.part x y) ∧
      (∀ x y : (targets n).carrier,
        (T.stage (n+1)).raw.colour (q x) (q y) =
          (targets n).raw.colour x y)) :
    ∀ n : ℕ, ∃ e : (targets n).carrier → T.VertexLimit,
      Function.Injective e ∧
      (∀ x y : (targets n).carrier,
        T.limitRawPresentation.part (e x) (e y) ↔
          (targets n).raw.part x y) ∧
      (∀ x y : (targets n).carrier,
        T.limitRawPresentation.colour (e x) (e y) =
          (targets n).raw.colour x y) := by
  intro n
  obtain ⟨q, hInj, hPart, hColour⟩ := hTargets n
  let e : (targets n).carrier → T.VertexLimit :=
    fun x => T.vertexOf (n+1) (q x)
  refine ⟨e, (T.vertexOf_injective (n+1)).comp hInj, ?_, ?_⟩
  · intro x y
    exact (T.limitRawPresentation_part_iff (n+1) (q x) (q y)).trans
      (hPart x y)
  · intro x y
    exact (T.limitRawPresentation_colour_eq (n+1) (q x) (q y)).trans
      (hColour x y)

end SemigenericEPPA
