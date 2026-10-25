import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedAgeTargetSuccessor
import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerActualDLFCriterion
import SemigenericEPPA.Structure.DLFCountableRawAgeSchedule

/-!
# An ACTUAL countable finite group-action tower from unrestricted semi-coherence

A genuine unrestricted semi-coherent family consists of finite
raw R1--R3 structures with ARBITRARY (not necessarily locally safe)
finite subgroups of their ACTUAL E/R_c automorphism groups.

The certified finite age-target successor strengthens this family
without changing the selected finite action pairs. Classical
dependent choice along a prescribed countable raw-age schedule
produces a genuine FiniteRawActionPairTower in the same canonical
universe with strict old-group and vertex maps.

Every old partial raw automorphism is extended by a member of the
NEXT finite subgroup, and every scheduled finite raw target embeds
inducedly in that next finite structure. No good orbit or local
safety is used. The existing unrestricted quotient-colimit
construction is then able to deduce actual homogeneous DLF.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

/-- One finite raw subgroup-action pair together with evidence
that it lies in a given selected semi-coherent family. -/
structure FiniteSelectedRawActionState
    (d : RawDatum G C)
    (Selected : ∀ (V : Type (max u v)) [Finite V],
      FiniteRawActionPair d V → Prop) where
  carrier : Type (max u v)
  finite_carrier : Finite carrier
  pair : letI : Finite carrier := finite_carrier
    FiniteRawActionPair d carrier
  selected : letI : Finite carrier := finite_carrier
    Selected carrier pair

namespace FiniteSelectedRawActionState

variable {Selected : ∀ (V : Type (max u v)) [Finite V],
  FiniteRawActionPair d V → Prop}

/-- A selected true finite subgroup-action successor contains a
specified original-raw age target and extends every old partial
automorphism in the same genuine next-stage finite subgroup. -/
def HasTargetConnectorSuccessor
    (A B : FiniteSelectedRawActionState d Selected)
    (Q : FiniteRawAgeTarget d) : Prop :=
  letI : Finite A.carrier := A.finite_carrier
  letI : Finite B.carrier := B.finite_carrier
  ∃ (f : FiniteRawActionPairEmbedding A.pair B.pair)
    (q : Q.carrier → B.carrier),
    Function.Injective q ∧
    (∀ x y : Q.carrier,
      B.pair.raw.part (q x) (q y) ↔ Q.raw.part x y) ∧
    (∀ x y : Q.carrier,
      B.pair.raw.colour (q x) (q y) = Q.raw.colour x y) ∧
    (∀ (S : Set A.carrier) (p : S → A.carrier),
      Function.Injective p →
      (∀ x y : S,
        A.pair.raw.part x.val y.val ↔ A.pair.raw.part (p x) (p y)) →
      (∀ x y : S,
        A.pair.raw.colour (p x) (p y) =
          A.pair.raw.colour x.val y.val) →
      ∃ k : B.pair.subgroup,
        ∀ x : S,
          k.val.val (f.vertex x.val) = f.vertex (p x))

end FiniteSelectedRawActionState

/-- A genuinely unrestricted semi-coherent finite selected family
constructs an actual countable group-action tower realizing any
countable original-raw age schedule, with all old connectors.
No pre-existing infinite structure or group is assumed. -/
theorem exists_unrestrictedSemiCoherentTower_realizingAgeSchedule
    (d : RawDatum G C)
    (hSemi : d.HasFiniteRawSemiCoherentAgeTargetSuccessors)
    (targets : ℕ → FiniteRawAgeTarget d) :
    ∃ (V : ℕ → Type (max u v))
      (hV : ∀ n, Finite (V n)),
      letI : ∀ n, Finite (V n) := hV
      ∃ T : FiniteRawActionPairTower d V,
        T.HasNextStageRawConnectors ∧
        (∀ n : ℕ, ∃ q : (targets n).carrier → V (n+1),
          Function.Injective q ∧
          (∀ x y : (targets n).carrier,
            (T.stage (n+1)).raw.part (q x) (q y) ↔
              (targets n).raw.part x y) ∧
          (∀ x y : (targets n).carrier,
            (T.stage (n+1)).raw.colour (q x) (q y) =
              (targets n).raw.colour x y)) := by
  classical
  obtain ⟨Selected, hCofinal, hAgeTarget⟩ := hSemi
  let State := FiniteSelectedRawActionState d Selected
  let P₀ : RawRectanglePresentation d (ULift (Fin 0)) :=
    (emptyFiniteRaw (d := d)).pullbackRaw ULift.down
  obtain ⟨X, hX, A, _e, hSelected, _hInj, _hPart, _hColour⟩ :=
    hCofinal (ULift (Fin 0)) P₀
  letI : Finite X := hX
  let A₀ : State := {
    carrier := X
    finite_carrier := hX
    pair := A
    selected := hSelected
  }
  have hNext (S : State) (Q : FiniteRawAgeTarget d) :
      ∃ B : State, S.HasTargetConnectorSuccessor B Q := by
    letI : Finite S.carrier := S.finite_carrier
    letI : Fintype S.carrier := Fintype.ofFinite S.carrier
    letI : Finite Q.carrier := Q.finite_carrier
    letI : Fintype Q.carrier := Fintype.ofFinite Q.carrier
    obtain ⟨W, hW, B, f, q,
      hBSelected, hqInj, hqPart, hqColour, hPartials⟩ :=
      hAgeTarget S.carrier Q.carrier S.pair S.selected Q.raw
    letI : Finite W := hW
    let next : State := {
      carrier := W
      finite_carrier := hW
      pair := B
      selected := hBSelected
    }
    exact ⟨next, f, q, hqInj, hqPart, hqColour, hPartials⟩
  let next : State → FiniteRawAgeTarget d → State :=
    fun S Q => Classical.choose (hNext S Q)
  let states : ℕ → State :=
    Nat.rec A₀ (fun n S => next S (targets n))
  have hSucc (n : ℕ) :
      (states n).HasTargetConnectorSuccessor
        (states (n+1)) (targets n) := by
    change (states n).HasTargetConnectorSuccessor
      (next (states n) (targets n)) (targets n)
    exact Classical.choose_spec (hNext (states n) (targets n))
  let V : ℕ → Type (max u v) := fun n => (states n).carrier
  let hV : ∀ n, Finite (V n) := fun n => (states n).finite_carrier
  letI : ∀ n, Finite (V n) := hV
  let T : FiniteRawActionPairTower d V := {
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
  refine ⟨V, hV, T, ?_, ?_⟩
  · intro n S p hp hpPart hpColour
    obtain ⟨q, _hqInj, _hqPart, _hqColour, hPartials⟩ :=
      Classical.choose_spec (hSucc n)
    obtain ⟨k, hk⟩ := hPartials S p hp hpPart hpColour
    refine ⟨k, ?_⟩
    intro x
    change k.val.val
      ((T.vertexTransition n (n+1) (Nat.le_succ n)) x.val) =
      (T.vertexTransition n (n+1) (Nat.le_succ n)) (p x)
    rw [hStep n x.val, hStep n (p x)]
    exact hk x
  · intro n
    obtain ⟨q, hInj, hPart, hColour, _hOld⟩ :=
      Classical.choose_spec (hSucc n)
    exact ⟨q, hInj, hPart, hColour⟩

/-- Every scheduled original-raw finite target embeds inducedly
into the ACTUAL quotient vertex limit of an unrestricted tower. -/
theorem unrestrictedTower_ageSchedule_embedsInLimit
    {V : ℕ → Type (max u v)}
    [∀ n, Finite (V n)]
    (T : FiniteRawActionPairTower d V)
    (targets : ℕ → FiniteRawAgeTarget d)
    (hTargets : ∀ n : ℕ,
      ∃ q : (targets n).carrier → V (n+1),
        Function.Injective q ∧
        (∀ x y : (targets n).carrier,
          (T.stage (n+1)).raw.part (q x) (q y) ↔
            (targets n).raw.part x y) ∧
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
