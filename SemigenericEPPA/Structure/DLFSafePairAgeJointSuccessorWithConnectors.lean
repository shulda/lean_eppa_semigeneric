import SemigenericEPPA.Structure.DLFSafePairAgeJointSuccessor
import SemigenericEPPA.Structure.DLFInducedPartialConnectorTransport

/-!
# Age-target finite safe successor with ALL old partial connectors

The finite safe-pair construction over arbitrary age superstructures
produces one finite subgroup K realizing all partial automorphisms
of the WHOLE intermediate raw structure. Unconditional JEP adjoins
any prescribed finite target Q to an old safe (A,H).

The certified induced-partial-connector transport lemma restricts
these full-intermediate connectors to every old partial raw
automorphism of A. Thus ONE finite safe (B,K) now simultaneously:

* extends the genuine H action strictly and injectively;
* contains an induced copy of arbitrary finite target Q;
* extends every old partial raw automorphism of A by an element
  of the SAME actual finite subgroup K.

This is the exact SINGLE-STEP ingredient needed for a countable,
age-cofinal tower with all next-stage connector requirements.
It assumes one complete good affine congruence orbit, not global
congruence saturation; no SAP or Fraïssé existence is used here.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {V : Type w} [Fintype V]
variable {W : Type t} [Fintype W]
variable {d : RawDatum G C}

namespace FiniteSafeRawPair

/-- A prescribed age target and ALL old partial raw connectors can
be realized by the same successor finite safe subgroup, with strict
old action equivariance and exact original E/R_c embeddings. -/
theorem exists_safeExtension_containingFiniteRaw_withConnectors
    (A : FiniteSafeRawPair d V)
    (Q : RawRectanglePresentation d W)
    (hOrbit : d.HasCompleteGoodOrbit) :
    ∃ (Z : Type (max u (max v (max (max w t) w))))
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
    A.exists_safeExtension_overRawEmbedding
      R Sum.inl hInj hPart hColour hOrbit
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
