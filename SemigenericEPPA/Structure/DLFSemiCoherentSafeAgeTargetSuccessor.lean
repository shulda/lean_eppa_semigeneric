import SemigenericEPPA.Structure.DLFCofinalSafeFiniteActionProperty
import SemigenericEPPA.Structure.DLFInducedPartialConnectorTransport
import SemigenericEPPA.Structure.DisjointRawJointEmbedding

/-!
# Semi-coherent safe-family axiom: add any age target and all connectors

Given the explicit cofinal safe finite group action extension
property, the prescribed age target Q can be freely joined with
the original finite safe pair A via disjoint raw amalgamation.
The relative family extension is then applied to the whole
A ⊕ Q (with NO old H-action on its Q-side).

The induced-partial-connector transport lemma restricts all
partial automorphisms of that intermediate raw structure to the
old A. One finite safe subgroup K simultaneously extends the
old group strictly, contains the chosen age target and realizes
every original partial automorphism of A.

This is exactly the finite successor needed to derive a countable
homogeneous DLF witness DIRECTLY from the finite semi-coherent
safe-family property, independently of either good-orbit
positive construction. Does not assume Sagi's general theorem.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {V W : Type (max u v)} [Fintype V] [Fintype W]
variable {d : RawDatum G C}

namespace FiniteSafeRawPair

/-- A prescribed age target and ALL old partial raw connectors can
be realized by the same successor finite safe subgroup, with strict
old action equivariance and exact original E/R_c embeddings. -/
theorem exists_safeExtension_containingRaw_of_cofinalSafe
    (A : FiniteSafeRawPair d V)
    (Q : RawRectanglePresentation d W)
    (hCofinal : d.HasCofinalSafeFiniteGroupExtension) :
    ∃ (Z : Type (max u v))
      (hZ : Finite Z),
      letI : Finite Z := hZ
      ∃ (B : FiniteSafeRawPair d Z)
        (f : FiniteSafeRawPairEmbedding A B)
        (q : W → Z),
        Function.Injective q ∧
        (∀ x y : W, B.raw.part (q x) (q y) ↔ Q.part x y) ∧
        (∀ x y : W, B.raw.colour (q x) (q y) = Q.colour x y) ∧
        (∀ (S : Set V) (p : S → V),
          Function.Injective p →
          (∀ x y : S, A.raw.part x.val y.val ↔
            A.raw.part (p x) (p y)) →
          (∀ x y : S, A.raw.colour (p x) (p y) =
            A.raw.colour x.val y.val) →
          ∃ k : B.subgroup,
            ∀ x : S, k.val.val (f.vertex x.val) = f.vertex (p x)) := by
  classical
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
  obtain ⟨Z, hZ, B, f, eR, hEInj, hEPart, hEColour,
      hOld, hPartials⟩ :=
    hCofinal.2 V (V ⊕ W) A R Sum.inl hInj hPart hColour
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
    ?_, ?_, ?_, hOldPartialExtension⟩
  · intro x y hxy
    apply Sum.inr.inj
    exact hEInj hxy
  · intro x y
    exact (hEPart (Sum.inr x) (Sum.inr y)).trans Iff.rfl
  · intro x y
    exact (hEColour (Sum.inr x) (Sum.inr y)).trans rfl


end FiniteSafeRawPair
end SemigenericEPPA
