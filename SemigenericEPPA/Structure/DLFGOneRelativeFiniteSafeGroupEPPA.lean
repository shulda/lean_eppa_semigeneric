import SemigenericEPPA.Structure.DLFGOneAutomaticRawSubgroupSafety
import SemigenericEPPA.Valuations.GOneActualRawAutSubgroupLifts
import SemigenericEPPA.Structure.DLFFiniteSafePairEmbeddings
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.End

/-!
# Exceptional G=1: relative finite safe-group EPPA with arbitrary selected H-action

For G=1 the exact fixed raw coherent witness already has BOTH:
all individual partial raw automorphisms of the entire old P,
and strict homomorphic extensions of an arbitrary H-action on
ANY induced old subset S⊆P, all inside its SAME finite original
raw automorphism group. There is no preexisting H action on P\S.

Choose that finite witness, extend the selected group H strictly
and injectively, and use its entire full raw automorphism group
as the acting finite subgroup. Since G is trivial, every actual
raw automorphism subgroup is automatically locally safe, even
when no globally self-reversing raw colour exists.

This theorem is the G=1 counterpart of the certified positive
relative safe-group EPPA theorem for a complete good affine
orbit. No good-orbit assumption and no global saturation occur.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {X : Type w} [Fintype X]
variable {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- G=1 relative raw EPPA: one finite actual raw witness contains
the whole original P, carries an injective strict action of an
arbitrary faithfully acting H on selected S, and extends EVERY
partial raw automorphism of the entire P in the same finite safe
subgroup. No HasCompleteGoodOrbit is assumed. -/
theorem exists_gOneRelativeFiniteSafeGroupEPPA
    (P : RawRectanglePresentation d X)
    (S : Set X)
    (rho : H →* Equiv.Perm S)
    (hFaithful : Function.Injective rho)
    (hPart : ∀ (h : H) (x y : S),
      P.part x.val y.val ↔
        P.part (rho h x).val (rho h y).val)
    (hColour : ∀ (h : H) (x y : S),
      P.colour (rho h x).val (rho h y).val =
        P.colour x.val y.val) :
    ∃ (W : Type (max v w)) (hW : Finite W),
      letI : Finite W := hW
      ∃ (B : FiniteSafeRawPair d W)
        (e : X → W)
        (theta : H →* B.subgroup),
        Function.Injective e ∧
        (∀ x y : X,
          B.raw.part (e x) (e y) ↔ P.part x y) ∧
        (∀ x y : X,
          B.raw.colour (e x) (e y) = P.colour x y) ∧
        Function.Injective theta ∧
        (∀ h : H, ∀ x : S,
          (theta h).val.val (e x.val) = e (rho h x).val) ∧
        (∀ (T : Set X) (p : T → X),
          Function.Injective p →
          (∀ x y : T, P.part x.val y.val ↔
            P.part (p x) (p y)) →
          (∀ x y : T, P.colour (p x) (p y) =
            P.colour x.val y.val) →
          ∃ k : B.subgroup,
            ∀ x : T, k.val.val (e x.val) = e (p x)) := by
  classical
  obtain ⟨j, K, hOldInj, hOldPart, hPartial, hGroups⟩ :=
    P.exists_gOneJointRawEPPA_andAllGroupLifts.{u, v, w, t}
  let W : Type (max v w) := GOneJointRawCarrier P
  letI : Finite (GOneFactorialCarrier P) := inferInstance
  letI : Finite (UniversalResidualCarrier C) :=
    finite_universalResidualCarrier
  have hW : Finite W := finite_rawCoverVertices
  letI : Finite W := hW
  let Q : RawRectanglePresentation d W :=
    P.gOneJointRawPresentation j K
  let e : X → W := P.gOneJointRawOldMap j
  have hInj : Function.Injective e := by
    intro x y hxy
    exact hOldInj (congrArg Prod.fst hxy)
  have hPartOld (x y : X) :
      Q.part (e x) (e y) ↔ P.part x y := by
    change P.gOneFactorialGeometry.part
      (P.gOneFactorialOldMap j x)
      (P.gOneFactorialOldMap j y) ↔ P.part x y
    exact hOldPart x y
  have hColourOld (x y : X) :
      Q.colour (e x) (e y) = P.colour x y := by
    exact K.old_colour x y
  obtain ⟨lift, hLiftOld⟩ :=
    P.exists_gOneRawSubgroupLift j K hGroups
      H S rho hPart hColour
  let B : FiniteSafeRawPair d W := Q.gOne_safePair ⊤
  let theta : H →* B.subgroup := {
    toFun := fun h => ⟨lift h, Subgroup.mem_top _⟩
    map_one' := by
      apply Subtype.ext
      exact map_one lift
    map_mul' := by
      intro h k
      apply Subtype.ext
      exact map_mul lift h k
  }
  have hThetaInj : Function.Injective theta := by
    intro h k heq
    have hh : lift h = lift k := congrArg Subtype.val heq
    apply hFaithful
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply hInj
    calc
      e (rho h x).val = (lift h).val (e x.val) :=
        (hLiftOld h x).symm
      _ = (lift k).val (e x.val) := by rw [hh]
      _ = e (rho k x).val := hLiftOld k x
  refine ⟨W, hW, B, e, theta, hInj,
    hPartOld, hColourOld, hThetaInj, ?_, ?_⟩
  · intro h x
    exact hLiftOld h x
  · intro T p hp hpPart hpColour
    obtain ⟨perm, hOld, hPresE, hPresC⟩ :=
      hPartial T p hp hpPart hpColour
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

end RawRectanglePresentation
end SemigenericEPPA
