import SemigenericEPPA.Structure.DLFSemiCoherentSafeDLFClassification

/-!
# Unrestricted finite raw semi-coherent extension property

This module separates the genuine semi-coherent extension condition
from the SPECIAL cofinal family of locally safe finite actions used
to prove the positive DLF criterion.

A finite raw action pair consists of a literal R1--R3 original
E/R_c structure A and an ARBITRARY subgroup H of its actual full
raw automorphism group. No local involution safety is required.

A selected cofinal collection of such pairs must support:
1. induced copies of every finite raw age member;
2. over ANY induced embedding of a selected pair's underlying
   structure into an arbitrary age superstructure P (P need not
   carry any action by H), a larger selected pair (B,K);
3. a faithful group embedding H -> K, strict equivariance on all
   old vertices, and a single K extending every partial original
   raw automorphism of P.

This is precisely the finite group-action version of the
semi-coherent extension property in the manuscript, with carriers
in the common canonical witness universe. We prove its POSITIVE
direction using the already certified family of all safe pairs.
No converse or arbitrary-family classification is presumed.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

/-- An arbitrary finite original-raw structure together with an
arbitrary genuine automorphism subgroup, NOT required safe. -/
structure FiniteRawActionPair (d : RawDatum G C)
    (V : Type w) [Finite V] where
  raw : RawRectanglePresentation d V
  subgroup : Subgroup raw.fullRawAutGroup

namespace FiniteRawActionPair

variable {V : Type w} [Finite V]

/-- The local complete-good-orbit safety predicate for an
arbitrary finite raw action pair; the general semi-coherent
property below does NOT impose this on its selected family. -/
def IsSafe (A : FiniteRawActionPair d V) : Prop :=
  ∀ (h : A.subgroup), h * h = 1 →
    ∀ (x y : V), ¬A.raw.part x y →
      h.val.val x = y → h.val.val y = x →
        d.GoodCompleteOrbitAt (A.raw.effectiveReduct.F x y)

/-- A selected locally safe arbitrary pair is exactly a
FiniteSafeRawPair on the identical carrier and subgroup. -/
def toSafe (A : FiniteRawActionPair d V) (hSafe : A.IsSafe) :
    FiniteSafeRawPair d V where
  raw := A.raw
  subgroup := A.subgroup
  safe := hSafe

end FiniteRawActionPair

namespace FiniteSafeRawPair

variable {V : Type w} [Finite V]

/-- Forget ONLY the safety certificate, not the original relations
or the genuine finite automorphism subgroup. -/
def toRawActionPair (A : FiniteSafeRawPair d V) :
    FiniteRawActionPair d V where
  raw := A.raw
  subgroup := A.subgroup

theorem toRawActionPair_isSafe (A : FiniteSafeRawPair d V) :
    A.toRawActionPair.IsSafe := A.safe

end FiniteSafeRawPair

/-- Strict induced embeddings of arbitrary genuine original-raw
finite automorphism-action pairs. -/
structure FiniteRawActionPairEmbedding
    {V : Type w} [Finite V] {W : Type t} [Finite W]
    (A : FiniteRawActionPair d V)
    (B : FiniteRawActionPair d W) where
  vertex : V → W
  vertex_injective : Function.Injective vertex
  part_iff : ∀ x y : V,
    B.raw.part (vertex x) (vertex y) ↔ A.raw.part x y
  colour_eq : ∀ x y : V,
    B.raw.colour (vertex x) (vertex y) = A.raw.colour x y
  groupMap : A.subgroup →* B.subgroup
  group_injective : Function.Injective groupMap
  group_action : ∀ (h : A.subgroup) (x : V),
    (groupMap h).val.val (vertex x) = vertex (h.val.val x)

namespace FiniteSafeRawPairEmbedding

variable {V : Type w} [Finite V]
variable {W : Type t} [Finite W]
variable {A : FiniteSafeRawPair d V}
variable {B : FiniteSafeRawPair d W}

/-- A genuine equivariant safe-pair embedding remains a strict
equivariant embedding after forgetting the safety certificates. -/
def toRawActionPairEmbedding
    (f : FiniteSafeRawPairEmbedding A B) :
    FiniteRawActionPairEmbedding A.toRawActionPair B.toRawActionPair where
  vertex := f.vertex
  vertex_injective := f.vertex_injective
  part_iff := f.part_iff
  colour_eq := f.colour_eq
  groupMap := f.groupMap
  group_injective := f.group_injective
  group_action := f.group_action

end FiniteSafeRawPairEmbedding

namespace RawDatum

/-- The UNRESTRICTED finite original-raw semi-coherent EP property:
there exists an arbitrary cofinal selected family of genuine finite
group-action pairs, not necessarily locally safe, admitting strict
relative group extensions and all partial-map connectors.

The carrier universe is fixed at max u v, matching the actual
witness constructions and avoiding implicit enlargement across
universes. -/
def HasFiniteRawSemiCoherentEP (d : RawDatum G C) : Prop :=
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
    (∀ (V X : Type (max u v)) [Finite V] [Finite X]
      (A : FiniteRawActionPair d V),
      Selected V A →
      ∀ (P : RawRectanglePresentation d X)
        (e0 : V → X)
        (he0inj : Function.Injective e0)
        (he0part : ∀ x y : V,
          P.part (e0 x) (e0 y) ↔ A.raw.part x y)
        (he0colour : ∀ x y : V,
          P.colour (e0 x) (e0 y) = A.raw.colour x y),
        ∃ (W : Type (max u v)) (hW : Finite W),
          letI : Finite W := hW
          ∃ (B : FiniteRawActionPair d W)
            (f : FiniteRawActionPairEmbedding A B)
            (eP : X → W),
            Selected W B ∧
            Function.Injective eP ∧
            (∀ x y : X,
              B.raw.part (eP x) (eP y) ↔ P.part x y) ∧
            (∀ x y : X,
              B.raw.colour (eP x) (eP y) = P.colour x y) ∧
            (∀ x : V, f.vertex x = eP (e0 x)) ∧
            (∀ (T : Set X) (p : T → X),
              Function.Injective p →
              (∀ x y : T,
                P.part x.val y.val ↔ P.part (p x) (p y)) →
              (∀ x y : T,
                P.colour (p x) (p y) =
                  P.colour x.val y.val) →
              ∃ k : B.subgroup,
                ∀ x : T, k.val.val (eP x.val) = eP (p x)))

/-- The CI-certified cofinal family of ALL locally safe original
raw group-action pairs is a concrete witness to the unrestricted
semi-coherent extension property. No new restriction is added to
the definition of the target property. -/
theorem hasFiniteRawSemiCoherentEP_of_cofinalSafe
    (d : RawDatum G C)
    (hSafe : d.HasCofinalSafeFiniteGroupExtension) :
    d.HasFiniteRawSemiCoherentEP := by
  classical
  refine ⟨(fun V _ A => A.IsSafe), ?_, ?_⟩
  · intro X _ P
    let S : FiniteSafeRawPair d X := P.trivialSafePair
    let B : FiniteRawActionPair d X := S.toRawActionPair
    refine ⟨X, inferInstance, B, id,
      S.toRawActionPair_isSafe, Function.injective_id, ?_, ?_⟩
    · intro x y
      exact Iff.rfl
    · intro x y
      rfl
  · intro V X _ _ A hSelected P e0 hInj hPart hColour
    let S : FiniteSafeRawPair d V := A.toSafe hSelected
    obtain ⟨W, hW, B, f, eP,
      hePInj, hePPart, hePColour, hOld, hPartials⟩ :=
      hSafe.2 V X S P e0 hInj hPart hColour
    letI : Finite W := hW
    let B0 : FiniteRawActionPair d W := B.toRawActionPair
    let f0 : FiniteRawActionPairEmbedding A B0 :=
      f.toRawActionPairEmbedding
    exact ⟨W, hW, B0, f0, eP,
      B.toRawActionPair_isSafe,
      hePInj, hePPart, hePColour, hOld, hPartials⟩

/-- Algebraic DLF criterion supplies an actual arbitrary-family
semi-coherent witness; the finite group-action family used for
this positive implication happens to be safe. -/
theorem hasFiniteRawSemiCoherentEP_of_dlfCriterion
    (d : RawDatum G C)
    (h : Subsingleton G ∨ d.HasCompleteGoodOrbit) :
    d.HasFiniteRawSemiCoherentEP :=
  d.hasFiniteRawSemiCoherentEP_of_cofinalSafe
    (d.hasCofinalSafeFiniteGroupExtension_of_dlfCriterion h)

/-- In particular the existence of a genuine homogeneous full-age
DLF model implies the general finite raw semi-coherent EP
property of the class, via the already certified DLF criterion. -/
theorem hasFiniteRawSemiCoherentEP_of_dlf
    (d : RawDatum G C)
    (hDLF : d.HasCountableHomogeneousDLF) :
    d.HasFiniteRawSemiCoherentEP :=
  d.hasFiniteRawSemiCoherentEP_of_dlfCriterion
    ((d.countableHomogeneousDLF_iff).mp hDLF)

end RawDatum
end SemigenericEPPA
