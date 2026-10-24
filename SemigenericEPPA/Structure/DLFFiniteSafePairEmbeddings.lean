import SemigenericEPPA.Structure.RawPresentationEffectiveBridge
import SemigenericEPPA.Structure.DLFFullRawAutomorphismGroup
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport

/-!
# Genuine finite safe pairs and strict equivariant embeddings

The finite semi-coherent positive DLF induction runs through pairs
(A,H), where A is a finite original R1--R3 raw rectangle and
H≤Aut_raw(A) is a *genuine* finite subgroup acting faithfully
on A, such that every H-involution reversing any E-cross pair
does so at an effective colour whose entire affine congruence
orbit is good.

A morphism (A,H)→(B,K) must consist of:
* one injective induced embedding e:A→B preserving and reflecting
  the original E and EVERY raw R_c predicate;
* one injective group homomorphism theta:H→K;
* exact equivariance theta(h)(e(x)) = e(h(x)) for EVERY old x.

Neither a subgroup of abstract effective-colour permutations nor
an arbitrary set-map lift is sufficient for the subsequent limit.
This module packages the exact pair/morphism interface and
certifies identity and composition. It does NOT yet construct
an infinite chain or a DLF subgroup of a Fraïssé limit.
-/

namespace SemigenericEPPA

universe u v w w' w''
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}

/-- A finite raw presentation and a subgroup of its actual full
original E/R_c automorphism group, with the local complete-good-orbit
condition on every square-one element exchanging a cross-E pair.
Group finiteness is automatic from the finite vertex carrier. -/
structure FiniteSafeRawPair (d : RawDatum G C)
    (V : Type w) [Finite V] where
  raw : RawRectanglePresentation d V
  subgroup : Subgroup raw.fullRawAutGroup
  safe : ∀ (h : subgroup), h * h = 1 →
    ∀ (x y : V), ¬raw.part x y →
      h.val.val x = y → h.val.val y = x →
        d.GoodCompleteOrbitAt (raw.effectiveReduct.F x y)

namespace FiniteSafeRawPair

variable {V : Type w} [Finite V]

/-- The selected actual original-language automorphism subgroup
has finite carrier, with NO extra finiteness hypothesis on H. -/
theorem finite_subgroup (A : FiniteSafeRawPair d V) :
    Finite A.subgroup := by
  classical
  letI : Finite A.raw.fullRawAutGroup :=
    A.raw.finite_fullRawAutGroup
  infer_instance

end FiniteSafeRawPair

/-- Faithful strict morphism of genuine original-language
finite safe pairs. The group homomorphism is injective and its
action agrees exactly on the embedded whole old carrier. -/
structure FiniteSafeRawPairEmbedding
    {V : Type w} [Finite V] {W : Type w'} [Finite W]
    (A : FiniteSafeRawPair d V)
    (B : FiniteSafeRawPair d W) where
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
variable {W : Type w'} [Finite W]
variable {X : Type w''} [Finite X]
variable {A : FiniteSafeRawPair d V}
variable {B : FiniteSafeRawPair d W}
variable {D : FiniteSafeRawPair d X}

/-- Identity safe-pair morphism in the actual raw language. -/
def refl (A : FiniteSafeRawPair d V) :
    FiniteSafeRawPairEmbedding A A where
  vertex := id
  vertex_injective := Function.injective_id
  part_iff := by
    intro x y
    exact Iff.rfl
  colour_eq := by
    intro x y
    rfl
  groupMap := MonoidHom.id A.subgroup
  group_injective := by
    intro h k hh
    exact hh
  group_action := by
    intro h x
    rfl

/-- Composition respects BOTH strict group laws and the literal
original vertex relations, and is equivariant on every old vertex. -/
def comp
    (f : FiniteSafeRawPairEmbedding A B)
    (g : FiniteSafeRawPairEmbedding B D) :
    FiniteSafeRawPairEmbedding A D where
  vertex := fun x => g.vertex (f.vertex x)
  vertex_injective := g.vertex_injective.comp f.vertex_injective
  part_iff := by
    intro x y
    exact (g.part_iff (f.vertex x) (f.vertex y)).trans (f.part_iff x y)
  colour_eq := by
    intro x y
    exact (g.colour_eq (f.vertex x) (f.vertex y)).trans (f.colour_eq x y)
  groupMap := g.groupMap.comp f.groupMap
  group_injective := g.group_injective.comp f.group_injective
  group_action := by
    intro h x
    change (g.groupMap (f.groupMap h)).val.val (g.vertex (f.vertex x)) =
      g.vertex (f.vertex (h.val.val x))
    rw [g.group_action (f.groupMap h) (f.vertex x), f.group_action h x]

/-- Literal vertex map of a composed safe-pair embedding. -/
theorem comp_vertex_apply
    (f : FiniteSafeRawPairEmbedding A B)
    (g : FiniteSafeRawPairEmbedding B D)
    (x : V) :
    (comp f g).vertex x = g.vertex (f.vertex x) := rfl

/-- Literal group map of a composed safe-pair embedding. -/
theorem comp_group_apply
    (f : FiniteSafeRawPairEmbedding A B)
    (g : FiniteSafeRawPairEmbedding B D)
    (h : A.subgroup) :
    (comp f g).groupMap h = g.groupMap (f.groupMap h) := rfl

end FiniteSafeRawPairEmbedding
end SemigenericEPPA
