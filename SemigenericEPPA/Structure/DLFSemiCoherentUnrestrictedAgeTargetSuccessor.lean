import SemigenericEPPA.Structure.DLFFiniteUnrestrictedSemiCoherentEP
import SemigenericEPPA.Structure.DLFInducedPartialConnectorTransport
import SemigenericEPPA.Structure.DisjointRawJointEmbedding

/-!
# Unrestricted semi-coherent age-target finite successor

The finite semi-coherent extension property selects arbitrary
finite raw group-action pairs (A,H) without any involution
safety certificate. In order to construct an age-cofinal tower,
we strengthen its chosen family to an age-target successor rule.

Given a selected (A,H) and arbitrary finite original raw target Q,
form the unconditional disjoint raw joint R=A ⊕ Q, extend the
selected H action over A -> R using semi-coherence, and restrict
the resulting group connectors for all partial automorphisms
of R back to A.

The same finite subgroup K in the successor realizes the entire
prescribed Q and all old A partial maps; old H persists strictly
and faithfully. No affine good-orbit hypothesis is used.
This is the direct finite stage of the general Sagi construction,
specialized to the original semigeneric R1--R3 language.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

namespace RawDatum

/-- A cofinal arbitrary family of genuine original-raw group
pairs with a stronger finite successor clause: add ANY finite
age target and extend ALL old partial raw automorphisms in
the same finite new group, strictly preserving old H. -/
def HasFiniteRawSemiCoherentAgeTargetSuccessors
    (d : RawDatum G C) : Prop :=
  ∃ (Selected : ∀ (V : Type (max u v)) [Finite V],
      FiniteRawActionPair d V → Prop),
    (∀ (X : Type (max u v)) [Finite X]
      (P : RawRectanglePresentation d X),
      ∃ (W : Type (max u v)) (hW : Finite W),
        letI : Finite W := hW
        ∃ (B : FiniteRawActionPair d W) (e : X → W),
          Selected W B ∧
          Function.Injective e ∧
          (∀ x y : X,
            B.raw.part (e x) (e y) ↔ P.part x y) ∧
          (∀ x y : X,
            B.raw.colour (e x) (e y) = P.colour x y)) ∧
    (∀ (V W : Type (max u v)) [Fintype V] [Fintype W]
      (A : FiniteRawActionPair d V),
      Selected V A →
      ∀ (Q : RawRectanglePresentation d W),
        ∃ (Z : Type (max u v)) (hZ : Finite Z),
          letI : Finite Z := hZ
          ∃ (B : FiniteRawActionPair d Z)
            (f : FiniteRawActionPairEmbedding A B)
            (q : W → Z),
            Selected Z B ∧
            Function.Injective q ∧
            (∀ x y : W,
              B.raw.part (q x) (q y) ↔ Q.part x y) ∧
            (∀ x y : W,
              B.raw.colour (q x) (q y) = Q.colour x y) ∧
            (∀ (S : Set V) (p : S → V),
              Function.Injective p →
              (∀ x y : S,
                A.raw.part x.val y.val ↔ A.raw.part (p x) (p y)) →
              (∀ x y : S,
                A.raw.colour (p x) (p y) =
                  A.raw.colour x.val y.val) →
              ∃ k : B.subgroup,
                ∀ x : S,
                  k.val.val (f.vertex x.val) = f.vertex (p x)))

/-- An unrestricted cofinal semi-coherent family automatically
has simultaneous prescribed age-target extensions and old
partial-map connectors. The SAME original selected family works;
NO safety modification or enlargement of the family is needed. -/
theorem hasAgeTargetSuccessors_of_finiteRawSemiCoherentEP
    (d : RawDatum G C)
    (hSemi : d.HasFiniteRawSemiCoherentEP) :
    d.HasFiniteRawSemiCoherentAgeTargetSuccessors := by
  classical
  obtain ⟨Selected, hCofinal, hExtension⟩ := hSemi
  refine ⟨Selected, hCofinal, ?_⟩
  intro V W _ _ A hSelected Q
  let c : C := Classical.choose (d.phi_surjective 1)
  let R : RawRectanglePresentation d (V ⊕ W) :=
    A.raw.disjointJoint Q c
  have hInj : Function.Injective (Sum.inl : V → V ⊕ W) := by
    intro x y h
    exact Sum.inl.inj h
  have hPart : ∀ x y : V,
      R.part (Sum.inl x) (Sum.inl y) ↔ A.raw.part x y := by
    intro x y
    exact Iff.rfl
  have hColour : ∀ x y : V,
      R.colour (Sum.inl x) (Sum.inl y) =
        A.raw.colour x y := by
    intro x y
    rfl
  obtain ⟨Z, hZ, B, f, eR,
      hSelectedB, hEInj, hEPart, hEColour, hOld, hPartials⟩ :=
    hExtension V (V ⊕ W) A hSelected R Sum.inl
      hInj hPart hColour
  letI : Finite Z := hZ
  have hOldConnectors : ∀ (S : Set V) (p : S → V),
      Function.Injective p →
      (∀ x y : S, A.raw.part x.val y.val ↔
        A.raw.part (p x) (p y)) →
      (∀ x y : S, A.raw.colour (p x) (p y) =
        A.raw.colour x.val y.val) →
      ∃ k : B.subgroup,
        ∀ x : S, k.val.val (eR (Sum.inl x.val)) =
          eR (Sum.inl (p x)) :=
    A.raw.partialConnectors_restrict_to_induced
      R Sum.inl hInj hPart hColour eR
      (K := B.subgroup) (fun k z => k.val.val z)
      hPartials
  have hOldPartialExtension :
      ∀ (S : Set V) (p : S → V),
        Function.Injective p →
        (∀ x y : S, A.raw.part x.val y.val ↔
          A.raw.part (p x) (p y)) →
        (∀ x y : S, A.raw.colour (p x) (p y) =
          A.raw.colour x.val y.val) →
        ∃ k : B.subgroup,
          ∀ x : S, k.val.val (f.vertex x.val) = f.vertex (p x) := by
    intro S p hp hpPart hpColour
    obtain ⟨k, hk⟩ :=
      hOldConnectors S p hp hpPart hpColour
    refine ⟨k, ?_⟩
    intro x
    calc
      k.val.val (f.vertex x.val) =
          k.val.val (eR (Sum.inl x.val)) :=
        congrArg (fun z => k.val.val z) (hOld x.val)
      _ = eR (Sum.inl (p x)) := hk x
      _ = f.vertex (p x) := (hOld (p x)).symm
  refine ⟨Z, hZ, B, f, (fun x : W => eR (Sum.inr x)),
    hSelectedB, ?_, ?_, ?_, hOldPartialExtension⟩
  · intro x y hxy
    apply Sum.inr.inj
    exact hEInj hxy
  · intro x y
    exact (hEPart (Sum.inr x) (Sum.inr y)).trans Iff.rfl
  · intro x y
    exact (hEColour (Sum.inr x) (Sum.inr y)).trans rfl

end RawDatum
end SemigenericEPPA
