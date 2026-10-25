import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitAutHom
import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerConditionalDensity

/-!
# Unrestricted semi-coherent actual automorphism limit: LimitHomogeneity

The stagewise safe-pair colimit theorem is replayed on an arbitrary
finite original-raw group-action tower. Its proof only uses strict
finite subgroup actions, induced E/R_c embeddings and the
next-stage partial connector property, not local involution safety.
No claim of tower existence is made in this module.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteRawActionPairTower

/-- Every finite original-language partial raw isomorphism of the
genuine quotient-limit R1–R3 structure extends to an element of
the ACTUAL full raw automorphism group of that infinite structure,
provided every finite tower stage has all next-stage connectors.

The input domain is a Finset of actual quotient vertices; the
map is an injective original E/R_c partial isomorphism. -/
theorem finiteRawPartialMap_extends_on_limit
    (T : FiniteRawActionPairTower d V)
    (hConn : T.HasNextStageRawConnectors)
    (F : Finset T.VertexLimit) (p : F → T.VertexLimit)
    (hpInj : Function.Injective p)
    (hpPart : ∀ x y : F,
      T.limitPart (p x) (p y) ↔ T.limitPart x.val y.val)
    (hpColour : ∀ x y : F,
      T.limitColour (p x) (p y) = T.limitColour x.val y.val) :
    ∃ a : T.limitRawPresentation.fullRawAutGroup,
      ∀ x : F, a.val x.val = p x := by
  classical
  let B : Finset T.VertexLimit := F ∪ F.attach.image p
  obtain ⟨n, hB⟩ := T.finiteSubset_supportedAtStage B
  let S : Set (V n) := {v | T.vertexOf n v ∈ F}
  let old : S → F := fun s => ⟨T.vertexOf n s.val, s.property⟩
  have hImage (s : S) :
      ∃ b : V n, T.vertexOf n b = p (old s) := by
    apply hB
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    exact ⟨old s, by simp, rfl⟩
  let q : S → V n := fun s => Classical.choose (hImage s)
  have hq (s : S) :
      T.vertexOf n (q s) = p (old s) :=
    Classical.choose_spec (hImage s)
  have hqInj : Function.Injective q := by
    intro a b hab
    have hpb : p (old a) = p (old b) :=
      (hq a).symm.trans ((congrArg (T.vertexOf n) hab).trans (hq b))
    have hOld : old a = old b := hpInj hpb
    apply Subtype.ext
    apply T.vertexOf_injective n
    exact congrArg Subtype.val hOld
  have hqPart : ∀ a b : S,
      (T.stage n).raw.part a.val b.val ↔
        (T.stage n).raw.part (q a) (q b) := by
    intro a b
    calc
      (T.stage n).raw.part a.val b.val ↔
          T.limitPart (T.vertexOf n a.val) (T.vertexOf n b.val) :=
        (T.limitPart_of n a.val b.val).symm
      _ ↔ T.limitPart (p (old a)) (p (old b)) :=
        (hpPart (old a) (old b)).symm
      _ ↔ (T.stage n).raw.part (q a) (q b) := by
        rw [← hq a, ← hq b]
        exact T.limitPart_of n (q a) (q b)
  have hqColour : ∀ a b : S,
      (T.stage n).raw.colour (q a) (q b) =
        (T.stage n).raw.colour a.val b.val := by
    intro a b
    calc
      (T.stage n).raw.colour (q a) (q b) =
          T.limitColour (T.vertexOf n (q a)) (T.vertexOf n (q b)) :=
        (T.limitColour_of n (q a) (q b)).symm
      _ = T.limitColour (p (old a)) (p (old b)) := by
        rw [hq a, hq b]
      _ = T.limitColour (T.vertexOf n a.val) (T.vertexOf n b.val) :=
        hpColour (old a) (old b)
      _ = (T.stage n).raw.colour a.val b.val :=
        T.limitColour_of n a.val b.val
  obtain ⟨k, hk⟩ := hConn n S q hqInj hqPart hqColour
  refine ⟨T.limitRawAutHom (T.groupOf (n+1) k), ?_⟩
  intro x
  obtain ⟨a, ha⟩ := hB x.val (Finset.mem_union_left _ x.property)
  have haF : T.vertexOf n a ∈ F := by
    rw [ha]
    exact x.property
  let s : S := ⟨a, haF⟩
  have hOld : old s = x := Subtype.ext ha
  change T.limitAct (T.groupOf (n+1) k) x.val = p x
  calc
    T.limitAct (T.groupOf (n+1) k) x.val =
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
          (T.vertexTransition n (n+1) (Nat.le_succ n) (q s)) :=
      congrArg (T.vertexOf (n+1)) (hk s)
    _ = T.vertexOf n (q s) :=
      T.vertexOf_transition n (n+1) (Nat.le_succ n) (q s)
    _ = p (old s) := hq s
    _ = p x := congrArg p hOld

end FiniteRawActionPairTower
end SemigenericEPPA
