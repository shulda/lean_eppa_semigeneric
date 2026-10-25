import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerFiniteSupport
import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitRawData
import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitAction

/-!
# Unrestricted semi-coherent actual automorphism limit: ConditionalDensity

The stagewise safe-pair colimit theorem is replayed on an arbitrary
finite original-raw group-action tower. Its proof only uses strict
finite subgroup actions, induced E/R_c embeddings and the
next-stage partial connector property, not local involution safety.
No claim of tower existence is made in this module.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G] {C : Type v} [Finite C]
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteRawActionPairTower

/-- Each original partial automorphism at stage n extends to ONE
element of the actual safe finite subgroup at stage n+1, via the
genuine strict n→n+1 embedding. -/
def HasNextStageRawConnectors (T : FiniteRawActionPairTower d V) : Prop :=
  ∀ (n : ℕ) (S : Set (V n)) (p : S → V n),
    Function.Injective p →
    (∀ x y : S, (T.stage n).raw.part x.val y.val ↔
      (T.stage n).raw.part (p x) (p y)) →
    (∀ x y : S, (T.stage n).raw.colour (p x) (p y) =
      (T.stage n).raw.colour x.val y.val) →
    ∃ k : (T.stage (n+1)).subgroup, ∀ x : S,
      k.val.val (T.vertexTransition n (n+1) (Nat.le_succ n) x.val) =
        T.vertexTransition n (n+1) (Nat.le_succ n) (p x)

/-- Exact finite-restriction approximation of every automorphism
of the quotient original raw E/R_c data by a GROUP-COLIMIT element.
This is the density implication once the limit action is faithful
and embedded in its actual original-language automorphism group. -/
theorem finiteRestrictionApprox_of_nextStageRawConnectors
    (T : FiniteRawActionPairTower d V)
    (hConn : T.HasNextStageRawConnectors)
    (alpha : Equiv.Perm T.VertexLimit)
    (hPart : ∀ x y : T.VertexLimit,
      T.limitPart (alpha x) (alpha y) ↔ T.limitPart x y)
    (hColour : ∀ x y : T.VertexLimit,
      T.limitColour (alpha x) (alpha y) = T.limitColour x y)
    (F : Finset T.VertexLimit) :
    ∃ g : T.GroupLimit,
      ∀ z : T.VertexLimit, z ∈ F → T.limitAct g z = alpha z := by
  classical
  let B : Finset T.VertexLimit := F ∪ F.image alpha
  obtain ⟨n, hB⟩ := T.finiteSubset_supportedAtStage B
  let S : Set (V n) := {a | T.vertexOf n a ∈ F}
  have hImage : ∀ a : S,
      ∃ b : V n, T.vertexOf n b = alpha (T.vertexOf n a.val) := by
    intro a
    apply hB
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    exact ⟨T.vertexOf n a.val, a.property, rfl⟩
  let p : S → V n := fun a => Classical.choose (hImage a)
  have hp (a : S) :
      T.vertexOf n (p a) = alpha (T.vertexOf n a.val) :=
    Classical.choose_spec (hImage a)
  have hpInj : Function.Injective p := by
    intro a b hab
    apply Subtype.ext
    apply T.vertexOf_injective n
    apply alpha.injective
    calc
      alpha (T.vertexOf n a.val) = T.vertexOf n (p a) := (hp a).symm
      _ = T.vertexOf n (p b) := congrArg (T.vertexOf n) hab
      _ = alpha (T.vertexOf n b.val) := hp b
  have hpPart : ∀ a b : S,
      (T.stage n).raw.part a.val b.val ↔
        (T.stage n).raw.part (p a) (p b) := by
    intro a b
    calc
      (T.stage n).raw.part a.val b.val ↔
          T.limitPart (T.vertexOf n a.val) (T.vertexOf n b.val) :=
        (T.limitPart_of n a.val b.val).symm
      _ ↔ T.limitPart (alpha (T.vertexOf n a.val))
            (alpha (T.vertexOf n b.val)) :=
        (hPart (T.vertexOf n a.val) (T.vertexOf n b.val)).symm
      _ ↔ (T.stage n).raw.part (p a) (p b) := by
        rw [←hp a, ←hp b]
        exact T.limitPart_of n (p a) (p b)
  have hpColour : ∀ a b : S,
      (T.stage n).raw.colour (p a) (p b) =
        (T.stage n).raw.colour a.val b.val := by
    intro a b
    calc
      (T.stage n).raw.colour (p a) (p b) =
          T.limitColour (T.vertexOf n (p a)) (T.vertexOf n (p b)) :=
        (T.limitColour_of n (p a) (p b)).symm
      _ = T.limitColour (alpha (T.vertexOf n a.val))
            (alpha (T.vertexOf n b.val)) := by
        rw [hp a, hp b]
      _ = T.limitColour (T.vertexOf n a.val) (T.vertexOf n b.val) :=
        hColour (T.vertexOf n a.val) (T.vertexOf n b.val)
      _ = (T.stage n).raw.colour a.val b.val :=
        T.limitColour_of n a.val b.val
  obtain ⟨k, hk⟩ := hConn n S p hpInj hpPart hpColour
  refine ⟨T.groupOf (n+1) k, ?_⟩
  intro z hz
  obtain ⟨a, ha⟩ := hB z (Finset.mem_union_left _ hz)
  have haF : T.vertexOf n a ∈ F := by
    rw [ha]
    exact hz
  let s : S := ⟨a, haF⟩
  calc
    T.limitAct (T.groupOf (n+1) k) z =
        T.limitAct (T.groupOf (n+1) k) (T.vertexOf n a) :=
      congrArg _ ha.symm
    _ = T.limitAct (T.groupOf (n+1) k)
          (T.vertexOf (n+1)
            (T.vertexTransition n (n+1) (Nat.le_succ n) a)) := by
      rw [T.vertexOf_transition n (n+1) (Nat.le_succ n) a]
    _ = T.vertexOf (n+1)
          (k.val.val (T.vertexTransition n (n+1) (Nat.le_succ n) a)) :=
      T.limitAct_of (n+1) k
        (T.vertexTransition n (n+1) (Nat.le_succ n) a)
    _ = T.vertexOf (n+1)
          (T.vertexTransition n (n+1) (Nat.le_succ n) (p s)) :=
      congrArg (T.vertexOf (n+1)) (hk s)
    _ = T.vertexOf n (p s) :=
      T.vertexOf_transition n (n+1) (Nat.le_succ n) (p s)
    _ = alpha (T.vertexOf n a) := hp s
    _ = alpha z := congrArg alpha ha

end FiniteRawActionPairTower
end SemigenericEPPA
