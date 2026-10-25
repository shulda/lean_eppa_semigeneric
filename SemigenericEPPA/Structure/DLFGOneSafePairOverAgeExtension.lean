import SemigenericEPPA.Structure.DLFGOneRelativeFiniteSafeGroupEPPA
import SemigenericEPPA.Structure.DLFFiniteSafePairEmbeddings
import Mathlib.Algebra.Group.End

/-!
# Exceptional G=1: relative finite safe-pair extension over arbitrary age superstructures

Under Subsingleton G, the strict relative finite safe-group EPPA constructor
extends any subgroup of the original raw automorphism group of A, even when
it has no action on the additional vertices of an arbitrary finite raw
superstructure P. Transport the original subgroup to the selected induced
old image S = range(e0), apply the G=1 relative finite construction, and
pull the strict group morphism and all partial connectors back to A.

The output is a genuine finite original-language safe-pair successor with
an induced embedding of the WHOLE P, strict equivariance on the old A, and
connectors for ALL partial raw automorphisms of P. No complete good orbit
or globally self-reversing raw colour is assumed.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {V : Type w} [Fintype V]
variable {X : Type t} [Fintype X]
variable {d : RawDatum G C}

namespace FiniteSafeRawPair

/-- Exceptional G=1 relative age-extension: strict old safe-group action, exact
whole-superstructure induced embedding, and all intermediate partial maps
are carried by one finite genuine safe raw subgroup. -/
theorem exists_gOneSafeExtension_overRawEmbedding
    (A : FiniteSafeRawPair d V)
    (P : RawRectanglePresentation d X)
    (e0 : V → X)
    (he0inj : Function.Injective e0)
    (he0part : ∀ x y : V,
      P.part (e0 x) (e0 y) ↔ A.raw.part x y)
    (he0colour : ∀ x y : V,
      P.colour (e0 x) (e0 y) = A.raw.colour x y) :
    ∃ (W : Type (max v t)) (hW : Finite W),
      letI : Finite W := hW
      ∃ (B : FiniteSafeRawPair d W)
        (f : FiniteSafeRawPairEmbedding A B)
        (eP : X → W),
        Function.Injective eP ∧
        (∀ x y : X,
          B.raw.part (eP x) (eP y) ↔ P.part x y) ∧
        (∀ x y : X,
          B.raw.colour (eP x) (eP y) = P.colour x y) ∧
        (∀ x : V, f.vertex x = eP (e0 x)) ∧
        (∀ (T : Set X) (p : T → X),
          Function.Injective p →
          (∀ x y : T, P.part x.val y.val ↔
            P.part (p x) (p y)) →
          (∀ x y : T, P.colour (p x) (p y) =
            P.colour x.val y.val) →
          ∃ k : B.subgroup,
            ∀ x : T, k.val.val (eP x.val) = eP (p x)) := by
  classical
  letI : Finite A.subgroup := A.finite_subgroup
  let S : Set X := Set.range e0
  let core : V → S := fun x => ⟨e0 x, ⟨x, rfl⟩⟩
  have hCoreInj : Function.Injective core := by
    intro x y hxy
    apply he0inj
    exact congrArg Subtype.val hxy
  have hCoreSurj : Function.Surjective core := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  let uEq : V ≃ S := Equiv.ofBijective core
    ⟨hCoreInj, hCoreSurj⟩
  have hUVal (x : V) : (uEq x).val = e0 x := rfl
  let rhoH : A.subgroup →* Equiv.Perm V :=
    A.raw.fullRawAutAction.comp A.subgroup.subtype
  let rhoS : A.subgroup →* Equiv.Perm S :=
    uEq.permCongrHom.toMonoidHom.comp rhoH
  have hMove (h : A.subgroup) (x : V) :
      rhoS h (uEq x) = uEq (h.val.val x) := by
    change uEq (rhoH h (uEq.symm (uEq x))) = uEq (h.val.val x)
    rw [uEq.symm_apply_apply]
    rfl
  have hFaithful : Function.Injective rhoS := by
    intro h k heq
    have hp : rhoH h = rhoH k :=
      uEq.permCongrHom.injective heq
    apply Subtype.ext
    apply Subtype.ext
    exact hp
  have hPart : ∀ (h : A.subgroup) (x y : S),
      P.part (rhoS h x).val (rhoS h y).val ↔
        P.part x.val y.val := by
    intro h x y
    obtain ⟨a, rfl⟩ := uEq.surjective x
    obtain ⟨b, rfl⟩ := uEq.surjective y
    rw [congrArg Subtype.val (hMove h a),
      congrArg Subtype.val (hMove h b)]
    change P.part (e0 (h.val.val a)) (e0 (h.val.val b)) ↔
      P.part (e0 a) (e0 b)
    exact (he0part (h.val.val a) (h.val.val b)).trans
      ((A.raw.fullRawAutGroup_part h.val a b).trans
        (he0part a b).symm)
  have hColour : ∀ (h : A.subgroup) (x y : S),
      P.colour (rhoS h x).val (rhoS h y).val =
        P.colour x.val y.val := by
    intro h x y
    obtain ⟨a, rfl⟩ := uEq.surjective x
    obtain ⟨b, rfl⟩ := uEq.surjective y
    rw [congrArg Subtype.val (hMove h a),
      congrArg Subtype.val (hMove h b)]
    change P.colour (e0 (h.val.val a)) (e0 (h.val.val b)) =
      P.colour (e0 a) (e0 b)
    exact (he0colour (h.val.val a) (h.val.val b)).trans
      ((A.raw.fullRawAutGroup_colour h.val a b).trans
        (he0colour a b).symm)

  obtain ⟨W, hFiniteW, B, eP, theta,
      hEInj, hEPart, hEColour,
      hThetaInj, hThetaOld, hPartials⟩ :=
    P.exists_gOneRelativeFiniteSafeGroupEPPA S rhoS hFaithful
      (fun h x y => (hPart h x y).symm) hColour
  letI : Finite W := hFiniteW
  let f : FiniteSafeRawPairEmbedding A B := {
    vertex := fun x => eP (e0 x)
    vertex_injective := hEInj.comp he0inj
    part_iff := by
      intro x y
      exact (hEPart (e0 x) (e0 y)).trans (he0part x y)
    colour_eq := by
      intro x y
      exact (hEColour (e0 x) (e0 y)).trans (he0colour x y)
    groupMap := theta
    group_injective := hThetaInj
    group_action := by
      intro h x
      calc
        (theta h).val.val (eP (e0 x)) =
            (theta h).val.val (eP (uEq x).val) := by rw [hUVal]
        _ = eP (rhoS h (uEq x)).val := hThetaOld h (uEq x)
        _ = eP (uEq (h.val.val x)).val :=
          congrArg eP (congrArg Subtype.val (hMove h x))
        _ = eP (e0 (h.val.val x)) := by rw [hUVal]
  }
  refine ⟨W, hFiniteW, B, f, eP,
    hEInj, hEPart, hEColour, ?_, ?_⟩
  · intro x
    rfl
  · exact hPartials

end FiniteSafeRawPair
end SemigenericEPPA
