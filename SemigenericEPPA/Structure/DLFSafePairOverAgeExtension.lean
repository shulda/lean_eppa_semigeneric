import SemigenericEPPA.Structure.DLFFiniteSafePairEmbeddings
import SemigenericEPPA.Structure.DLFFiniteSafeGroupEPPAExtension
import SemigenericEPPA.Structure.DLFInducedRawEffectiveReduct
import Mathlib.Algebra.Group.End

/-!
# Extend a finite safe pair across an arbitrary original-language age extension

The key induction step for an eventual dense locally finite automorphism
subgroup is stronger than EPPA of the old safe pair alone.

An old finite safe raw pair (A,H) may sit as an induced substructure
inside ANY finite raw P, with no H-action on the extra points of P.
This theorem extends the *full* P into a finite raw Q carrying one
finite safe subgroup K, and embeds H into K strictly equivariantly
on the original A, while also extending all partial automorphisms
of the enlarged intermediate P.

Transport of the action is through the literal image S = e(A)
and an actual equivalence A ≃ S. The safety condition is transferred
by equality of the canonical effective colours on induced old edges,
not by any auxiliary gauge or blanket saturation assumption.
The only algebraic hypothesis is ONE complete good affine orbit.

No countable limit or density theorem is asserted.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {V : Type w} [Fintype V]
variable {X : Type t} [Fintype X]
variable {d : RawDatum G C}

namespace FiniteSafeRawPair

/-- Genuine positive *relative-to-an-arbitrary-age-extension* step.

From a safe (A,H), an induced raw embedding A→P (where H need not
act on P), and a complete good affine orbit, construct a finite
safe (Q,K) containing P and a strict equivariant safe-pair morphism
(A,H)→(Q,K). The same K extends all partial raw maps of P. -/
theorem exists_safeExtension_overRawEmbedding
    (A : FiniteSafeRawPair d V)
    (P : RawRectanglePresentation d X)
    (e0 : V → X)
    (he0inj : Function.Injective e0)
    (he0part : ∀ x y : V,
      P.part (e0 x) (e0 y) ↔ A.raw.part x y)
    (he0colour : ∀ x y : V,
      P.colour (e0 x) (e0 y) = A.raw.colour x y)
    (hOrbit : d.HasCompleteGoodOrbit) :
    ∃ (W : Type (max u (max v (max t w)))) (hW : Finite W),
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
  have hSafe : ∀ (h : A.subgroup), h * h = 1 →
      ∀ (x y : S), ¬P.part x.val y.val →
        rhoS h x = y → rhoS h y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x.val y.val) := by
    intro h hh x y hcross hx hy
    obtain ⟨a, rfl⟩ := uEq.surjective x
    obtain ⟨b, rfl⟩ := uEq.surjective y
    have hcrossA : ¬A.raw.part a b := by
      intro hab
      exact hcross ((he0part a b).2 hab)
    have hxA : h.val.val a = b :=
      uEq.injective ((hMove h a).symm.trans hx)
    have hyA : h.val.val b = a :=
      uEq.injective ((hMove h b).symm.trans hy)
    change d.GoodCompleteOrbitAt
      (P.effectiveReduct.F (e0 a) (e0 b))
    rw [A.raw.effectiveReduct_crossColour_of_inducedRawColours
      P e0 he0colour a b hcrossA]
    exact A.safe h hh a b hcrossA hxA hyA
  obtain ⟨W, Pnew, eP, K, theta,
      hFiniteW, _hFiniteK, hEInj, hEPart, hEColour,
      hThetaInj, hThetaOld, hKSafe, hPartials⟩ :=
    P.exists_finiteSafeGroupEPPAExtension_of_completeGoodOrbit
      (H := A.subgroup) hOrbit S rhoS hFaithful
      hPart hColour hSafe
  letI : Finite W := hFiniteW
  let B : FiniteSafeRawPair d W := {
    raw := Pnew
    subgroup := K
    safe := hKSafe
  }
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
