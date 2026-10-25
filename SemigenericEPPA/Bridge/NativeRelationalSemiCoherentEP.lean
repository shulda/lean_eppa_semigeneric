import SemigenericEPPA.Bridge.RelationalFiniteSemiCoherentPairs
import SemigenericEPPA.Structure.PairwiseEmbedding
import SemigenericEPPA.Bridge.RawTypedEPPA

/-!
# Literal original-relational finite semi-coherent EP

A selected cofinal family of genuine pairs (A,H), where A is a
finite original E/R_c structure satisfying the actual R1--R3
axioms and H is a subgroup of the ORIGINAL relational full
automorphism group.

Relative extensions preserve every original binary relation,
give a faithful injective extension homomorphism H → K, and
extend ALL original-relational partial automorphisms of the
prescribed finite overstructure P into the SAME finite K.

Neither the selected family nor its finite subgroup actions are
assumed locally involution-safe. This is a standalone *native*
definition; its equivalence with the already certified
RawDatum.HasFiniteRawSemiCoherentEP is a subsequent bridge theorem.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t q

variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

/-- Strict induced embeddings of ACTUAL original-relational
finite subgroup-action pairs, with faithful group extension
and pointwise equivariance on the original carrier. -/
structure FiniteRelationalActionPairEmbedding
    {V : Type w} [Finite V] {W : Type t} [Finite W]
    (A : FiniteRelationalActionPair d V)
    (B : FiniteRelationalActionPair d W) where
  vertex : V → W
  vertex_injective : Function.Injective vertex
  part_iff : ∀ x y : V,
    partRel B.rel (vertex x) (vertex y) ↔ partRel A.rel x y
  raw_iff : ∀ (c : C) (x y : V),
    rawRel B.rel c (vertex x) (vertex y) ↔ rawRel A.rel c x y
  groupMap : A.subgroup →* B.subgroup
  group_injective : Function.Injective groupMap
  group_action : ∀ (h : A.subgroup) (x : V),
    (groupMap h).val.val (vertex x) = vertex (h.val.val x)

namespace FiniteRelationalActionPairEmbedding

variable {V : Type w} [Finite V]
variable {W : Type t} [Finite W]
variable {Q : Type q} [Finite Q]
variable {A : FiniteRelationalActionPair d V}
variable {B : FiniteRelationalActionPair d W}
variable {D : FiniteRelationalActionPair d Q}

/-- The relational induced vertex map is a genuine
AllThoseEPPA embedding with the identity language action. -/
def toStructureEmbedding
    (f : FiniteRelationalActionPairEmbedding A B) :
    Structure.Embedding (rectangleTrivialAction C) A.rel B.rel :=
  embeddingOfPairwiseEquiv (rectangleTrivialAction C)
    A.rel B.rel f.vertex f.vertex_injective f.part_iff f.raw_iff

/-- The identity finite original-relational action-pair morphism. -/
def refl (A : FiniteRelationalActionPair d V) :
    FiniteRelationalActionPairEmbedding A A where
  vertex := id
  vertex_injective := Function.injective_id
  part_iff := by intro x y; exact Iff.rfl
  raw_iff := by intro c x y; exact Iff.rfl
  groupMap := MonoidHom.id A.subgroup
  group_injective := by intro h k hhk; exact hhk
  group_action := by intro h x; rfl

/-- Composition preserves EXACT original E, all ordered R_c,
strict group injections, and equivariance of the old action. -/
def comp
    (f : FiniteRelationalActionPairEmbedding A B)
    (g : FiniteRelationalActionPairEmbedding B D) :
    FiniteRelationalActionPairEmbedding A D where
  vertex := fun x => g.vertex (f.vertex x)
  vertex_injective := g.vertex_injective.comp f.vertex_injective
  part_iff := by
    intro x y
    exact (g.part_iff (f.vertex x) (f.vertex y)).trans (f.part_iff x y)
  raw_iff := by
    intro c x y
    exact (g.raw_iff c (f.vertex x) (f.vertex y)).trans (f.raw_iff c x y)
  groupMap := g.groupMap.comp f.groupMap
  group_injective := g.group_injective.comp f.group_injective
  group_action := by
    intro h x
    change (g.groupMap (f.groupMap h)).val.val (g.vertex (f.vertex x)) =
      g.vertex (f.vertex (h.val.val x))
    rw [g.group_action (f.groupMap h) (f.vertex x), f.group_action h x]

end FiniteRelationalActionPairEmbedding

namespace RawDatum

/-- The fully NATIVE finite original-relational semi-coherent
extension property in the paper's binary E/R_c language.

There exists an arbitrary selected cofinal family of finite
relational subgroup actions (A,H) such that every induced
A→P extends to a selected (B,K) with H→K injective and
equivariant, and every finite original-relational partial
automorphism of P extends to one element of this K.

No safety assumption, no identification of raw colours in
different fibres, and no change of the original language. -/
def HasFiniteRelationalSemiCoherentEP
    (d : RawDatum G C) : Prop :=
  ∃ (Selected : ∀ (V : Type (max u v)) [Finite V],
      FiniteRelationalActionPair d V → Prop),
    (∀ (X : Type (max u v)) [Finite X]
      (P : Structure (rectangleLanguage C) X),
      IsRectangleStructure d P →
      ∃ (W : Type (max u v)) (hW : Finite W),
        letI : Finite W := hW
        ∃ (B : FiniteRelationalActionPair d W) (e : X → W),
          Selected W B ∧
          Function.Injective e ∧
          (∀ x y : X,
            partRel B.rel (e x) (e y) ↔ partRel P x y) ∧
          (∀ (c : C) (x y : X),
            rawRel B.rel c (e x) (e y) ↔ rawRel P c x y)) ∧
    (∀ (V X : Type (max u v)) [Finite V] [Finite X]
      (A : FiniteRelationalActionPair d V),
      Selected V A →
      ∀ (P : Structure (rectangleLanguage C) X),
        IsRectangleStructure d P →
      ∀ (e0 : V → X)
        (he0inj : Function.Injective e0)
        (he0part : ∀ x y : V,
          partRel P (e0 x) (e0 y) ↔ partRel A.rel x y)
        (he0raw : ∀ (c : C) (x y : V),
          rawRel P c (e0 x) (e0 y) ↔ rawRel A.rel c x y),
        ∃ (W : Type (max u v)) (hW : Finite W),
          letI : Finite W := hW
          ∃ (B : FiniteRelationalActionPair d W)
            (f : FiniteRelationalActionPairEmbedding A B)
            (eP : X → W),
            Selected W B ∧
            Function.Injective eP ∧
            (∀ x y : X,
              partRel B.rel (eP x) (eP y) ↔ partRel P x y) ∧
            (∀ (c : C) (x y : X),
              rawRel B.rel c (eP x) (eP y) ↔ rawRel P c x y) ∧
            (∀ x : V, f.vertex x = eP (e0 x)) ∧
            (∀ (T : Set X) (p : T → X),
              Function.Injective p →
              (∀ x y : T,
                partRel P x.val y.val ↔ partRel P (p x) (p y)) →
              (∀ (c : C) (x y : T),
                rawRel P c x.val y.val ↔ rawRel P c (p x) (p y)) →
              ∃ k : B.subgroup,
                ∀ x : T, k.val.val (eP x.val) = eP (p x)))

end RawDatum
end SemigenericEPPA
