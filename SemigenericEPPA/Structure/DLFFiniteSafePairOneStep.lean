import SemigenericEPPA.Structure.DLFFiniteSafePairEmbeddings
import SemigenericEPPA.Structure.DLFFiniteSafeGroupEPPAExtension
import Mathlib.Algebra.Group.End

/-!
# Positive DLF one-step extension of an actual finite safe raw pair

Under one complete good affine congruence orbit, an actual finite
safe pair (A,H) can be enlarged to another finite safe pair (B,K)
with a genuine induced raw embedding A→B and injective STRICTLY
EQUIVARIANT group map H→K.

The original relative safe EPPA theorem is formulated with a
selected subset S⊆A and an action on S. Here choose S=UNIV A
and transport the given faithful H≤Aut_raw(A) along the canonical
equivalence A ≃ (univ : Set A), without discarding any old vertex.

The same output subgroup K also extends EVERY partial raw
automorphism of the full old A, with no requirement that the
individual connectors be coherent. This is a constructive one-step
operation on the objects/morphisms of the finite-safe-pair
category. Iterating it in conjunction with finite age-extension
requirements is the next step toward a genuine DLF group tower.

No infinite Fraïssé limit or DLF density assertion occurs here.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {V : Type w} [Fintype V]
variable {d : RawDatum G C}

namespace FiniteSafeRawPair

/-- Exact one-step finite extension of a genuine safe pair,
including all old partial raw automorphism connectors.

The finite target vertex type W is chosen existentially, and its
Finite instance is part of the returned data. -/
theorem exists_safeExtension_withAllPartialMaps
    (A : FiniteSafeRawPair d V)
    (hOrbit : d.HasCompleteGoodOrbit) :
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
  letI : Finite A.subgroup := A.finite_subgroup
  let S : Set V := Set.univ
  let u : V ≃ S := {
    toFun := fun x => ⟨x, Set.mem_univ x⟩
    invFun := Subtype.val
    left_inv := by intro x; rfl
    right_inv := by intro x; cases x; rfl
  }
  let rhoH : A.subgroup →* Equiv.Perm V :=
    A.raw.fullRawAutAction.comp A.subgroup.subtype
  let rhoS : A.subgroup →* Equiv.Perm S :=
    u.permCongrHom.toMonoidHom.comp rhoH
  have hMove : ∀ (h : A.subgroup) (x : S),
      (rhoS h x).val = h.val.val x.val := by
    intro h x
    rfl
  have hFaithful : Function.Injective rhoS := by
    intro h k heq
    have hp : rhoH h = rhoH k :=
      u.permCongrHom.injective heq
    apply Subtype.ext
    apply Subtype.ext
    exact hp
  have hPart : ∀ (h : A.subgroup) (x y : S),
      A.raw.part (rhoS h x).val (rhoS h y).val ↔
        A.raw.part x.val y.val := by
    intro h x y
    rw [hMove h x, hMove h y]
    exact A.raw.fullRawAutGroup_part h.val x.val y.val
  have hColour : ∀ (h : A.subgroup) (x y : S),
      A.raw.colour (rhoS h x).val (rhoS h y).val =
        A.raw.colour x.val y.val := by
    intro h x y
    rw [hMove h x, hMove h y]
    exact A.raw.fullRawAutGroup_colour h.val x.val y.val
  have hSafe : ∀ (h : A.subgroup), h * h = 1 →
      ∀ (x y : S), ¬A.raw.part x.val y.val →
        rhoS h x = y → rhoS h y = x →
          d.GoodCompleteOrbitAt (A.raw.effectiveReduct.F x.val y.val) := by
    intro h hh x y hcross hx hy
    have hx' : h.val.val x.val = y.val :=
      (hMove h x).symm.trans (congrArg Subtype.val hx)
    have hy' : h.val.val y.val = x.val :=
      (hMove h y).symm.trans (congrArg Subtype.val hy)
    exact A.safe h hh x.val y.val hcross hx' hy'
  obtain ⟨W, Pnew, e, K, theta,
      hFiniteW, _hFiniteK, hEInj, hEPart, hEColour,
      hThetaInj, hThetaOld, hKSafe, hPartials⟩ :=
    A.raw.exists_finiteSafeGroupEPPAExtension_of_completeGoodOrbit
      (H := A.subgroup) hOrbit S rhoS hFaithful
      hPart hColour hSafe
  letI : Finite W := hFiniteW
  let B : FiniteSafeRawPair d W := {
    raw := Pnew
    subgroup := K
    safe := hKSafe
  }
  let f : FiniteSafeRawPairEmbedding A B := {
    vertex := e
    vertex_injective := hEInj
    part_iff := hEPart
    colour_eq := hEColour
    groupMap := theta
    group_injective := hThetaInj
    group_action := by
      intro h x
      have hx := hThetaOld h (u x)
      change (theta h).val.val (e x) = e (rhoS h (u x)).val at hx
      exact hx.trans (congrArg e (hMove h (u x)))
  }
  refine ⟨W, hFiniteW, B, f, ?_⟩
  intro T p hp hPartOld hColourOld
  exact hPartials T p hp hPartOld hColourOld

end FiniteSafeRawPair
end SemigenericEPPA
