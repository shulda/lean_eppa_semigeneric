import SemigenericEPPA.Structure.DLFGOneAutomaticRawSubgroupSafety
import SemigenericEPPA.Valuations.GOneActualRawAutSubgroupLifts
import SemigenericEPPA.Structure.DLFFiniteSafePairEmbeddings
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.End

/-!
# Finite safe-pair successor for the exceptional G=1 DLF branch

When the effective group G is trivial, the finite coherent raw
EPPA construction extends every old partial automorphism and,
on the SAME chosen finite raw witness, lifts every actual old
automorphism subgroup homomorphically.

Use the certified fixed G=1 factorial-plus-residual construction,
with its literal old raw zero-section. The old safe subgroup
H≤Aut_raw(A) acts strictly on the old copy, and the group
homomorphism into the full actual raw automorphism group of the
finite witness is injective because the old vertex embedding
is injective. All partial raw automorphisms of A also lift to
that same finite full automorphism group.

Crucially every genuine G=1 raw automorphism subgroup is
locally safe by the independently certified G=1 local-safety
lemma. NO complete good affine orbit is assumed, since the
raw alphabet may have NO reversal-fixed colour.

This is the finite successor for G=1. Combining it with
JEP/relative coherent-EPPA over age superstructures permits
the same countable DLF strategy, without false global
self-reversal assumptions.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {V : Type w} [Fintype V]
variable {d : RawDatum G C}

namespace FiniteSafeRawPair

/-- For trivial effective group G, ANY genuine finite safe pair
has one actual finite safe successor with a strict injective
group-action embedding and all old partial raw connectors.

No global good-orbit condition is imposed. -/
theorem exists_gOneSafeExtension_withAllPartialMaps
    (A : FiniteSafeRawPair d V) :
    ∃ (W : Type (max u (max v w))) (hW : Finite W),
      letI : Finite W := hW
      ∃ (B : FiniteSafeRawPair d W)
        (f : FiniteSafeRawPairEmbedding A B),
        ∀ (T : Set V) (p : T → V),
          Function.Injective p →
          (∀ x y : T, A.raw.part x.val y.val ↔
            A.raw.part (p x) (p y)) →
          (∀ x y : T, A.raw.colour (p x) (p y) =
            A.raw.colour x.val y.val) →
          ∃ k : B.subgroup,
            ∀ x : T, k.val.val (f.vertex x.val) = f.vertex (p x) := by
  classical
  let P := A.raw
  obtain ⟨j, K, hOldInj, hOldPart, hPartial, hGroups⟩ :=
    P.exists_gOneJointRawEPPA_andAllGroupLifts.{u, v, w, w}
  let W : Type (max u (max v w)) := GOneJointRawCarrier P
  letI : Finite (GOneFactorialCarrier P) := inferInstance
  letI : Finite (UniversalResidualCarrier C) :=
    finite_universalResidualCarrier
  have hW : Finite W := finite_rawCoverVertices
  letI : Finite W := hW
  let Q : RawRectanglePresentation d W :=
    P.gOneJointRawPresentation j K
  let ψ : V → W := P.gOneJointRawOldMap j
  have hψ : Function.Injective ψ := by
    intro x y hxy
    exact hOldInj (congrArg Prod.fst hxy)
  have hPartOld (x y : V) :
      Q.part (ψ x) (ψ y) ↔ P.part x y := by
    change P.gOneFactorialGeometry.part
      (P.gOneFactorialOldMap j x)
      (P.gOneFactorialOldMap j y) ↔ P.part x y
    exact hOldPart x y
  have hColourOld (x y : V) :
      Q.colour (ψ x) (ψ y) = P.colour x y := by
    exact K.old_colour x y
  let S : Set V := Set.univ
  let e : V ≃ S := {
    toFun := fun x => ⟨x, Set.mem_univ x⟩
    invFun := Subtype.val
    left_inv := by intro x; rfl
    right_inv := by intro x; cases x; rfl
  }
  let rhoH : A.subgroup →* Equiv.Perm V :=
    P.fullRawAutAction.comp A.subgroup.subtype
  let rhoS : A.subgroup →* Equiv.Perm S :=
    e.permCongrHom.toMonoidHom.comp rhoH
  have hMove (h : A.subgroup) (x : S) :
      (rhoS h x).val = h.val.val x.val := rfl
  have hE : ∀ (h : A.subgroup) (x y : S),
      P.part x.val y.val ↔
        P.part (rhoS h x).val (rhoS h y).val := by
    intro h x y
    rw [hMove h x, hMove h y]
    exact (P.fullRawAutGroup_part h.val x.val y.val).symm
  have hRaw : ∀ (h : A.subgroup) (x y : S),
      P.colour (rhoS h x).val (rhoS h y).val =
        P.colour x.val y.val := by
    intro h x y
    rw [hMove h x, hMove h y]
    exact P.fullRawAutGroup_colour h.val x.val y.val
  obtain ⟨lift, hLiftOld⟩ :=
    P.exists_gOneRawSubgroupLift j K hGroups
      A.subgroup S rhoS hE hRaw
  let B : FiniteSafeRawPair d W := Q.gOne_safePair ⊤
  let theta : A.subgroup →* B.subgroup := {
    toFun := fun h => ⟨lift h, Subgroup.mem_top _⟩
    map_one' := by
      apply Subtype.ext
      exact map_one lift
    map_mul' := by
      intro h k
      apply Subtype.ext
      exact map_mul lift h k
  }
  have hLiftInj : Function.Injective theta := by
    intro h k heq
    have heqLift : lift h = lift k :=
      congrArg Subtype.val heq
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply hψ
    calc
      ψ (h.val.val x) = (lift h).val (ψ x) := by
        have hh := hLiftOld h (e x)
        change (lift h).val (ψ x) =
          ψ (rhoS h (e x)).val at hh
        exact (congrArg ψ (hMove h (e x))).symm.trans hh.symm
      _ = (lift k).val (ψ x) := by rw [heqLift]
      _ = ψ (k.val.val x) := by
        have hh := hLiftOld k (e x)
        change (lift k).val (ψ x) =
          ψ (rhoS k (e x)).val at hh
        exact hh.trans (congrArg ψ (hMove k (e x)))
  let f : FiniteSafeRawPairEmbedding A B := {
    vertex := ψ
    vertex_injective := hψ
    part_iff := hPartOld
    colour_eq := hColourOld
    groupMap := theta
    group_injective := hLiftInj
    group_action := by
      intro h x
      have hh := hLiftOld h (e x)
      change (lift h).val (ψ x) =
        ψ (rhoS h (e x)).val at hh
      exact hh.trans (congrArg ψ (hMove h (e x)))
  }
  refine ⟨W, hW, B, f, ?_⟩
  intro T p hp hEp hCp
  obtain ⟨perm, hOld, hPresE, hPresC⟩ :=
    hPartial T p hp hEp hCp
  have hPres : PreservesBinaryRawRelations Q.part
      (fun c x y => Q.colour x y = some c) perm := by
    refine ⟨?_, ?_⟩
    · intro x y
      exact hPresE x y
    · intro c x y
      change Q.colour (perm x) (perm y) = some c ↔
        Q.colour x y = some c
      exact hPresC c x y
  let rawPerm : Q.fullRawAutGroup := ⟨perm, hPres⟩
  let k : B.subgroup := ⟨rawPerm, Subgroup.mem_top _⟩
  refine ⟨k, ?_⟩
  intro x
  exact hOld x

end FiniteSafeRawPair
end SemigenericEPPA
