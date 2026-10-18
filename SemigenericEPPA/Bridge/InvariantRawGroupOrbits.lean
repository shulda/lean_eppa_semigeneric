import SemigenericEPPA.Bridge.InvariantRawOrbitColours
import Mathlib.Data.Fintype.EquivFin

/-!
# H-invariant raw colouring from safe reversal orbits

Let a group H act on a finite set A of directed effective cross-pairs.
A raw edge colouring is H-invariant precisely when it factors through
the finite H-orbit quotient Q=A/H.

If reversal tau commutes with H and the effective colour f:A→G is
H-invariant and reverses by s, then both descend to Q. An orbit in
Q fixed by reversal has a representative a such that some h∈H
takes a to tau(a). Thus, if such reversed group orbits always
admit an actual self-reversing raw colour over f(a), the previously
verified involutive-orbit selection theorem produces an H-invariant
raw lift with the exact correct reversed raw colour.

This is the orbit-colouring input for the manuscript's
fixed-cover finite-group raw lift, abstracted from E and specific
vertex pairs. The next step instantiates A as ordered cross-part
pairs and derives its orbit safety from the hypothesis about H
elements interchanging their endpoints.
-/

namespace SemigenericEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {A : Type v}
variable {G : Type w} [Group G] {C : Type t}

/-- The orbit relation of a homomorphic permutation group action.
We specify it explicitly so no separate ambient MulAction instance
needs to be chosen on the finite edge-pair carrier. -/
private def permOrbitSetoid
    (rho : H →* Equiv.Perm A) : Setoid A where
  r a b := ∃ h : H, rho h a = b
  iseqv := by
    constructor
    · intro a
      refine ⟨1, ?_⟩
      simp
    · intro a b ⟨h, hb⟩
      refine ⟨h⁻¹, ?_⟩
      calc
        rho h⁻¹ b = rho h⁻¹ (rho h a) :=
          congrArg (rho h⁻¹) hb.symm
        _ = a := by
          rw [map_inv]
          exact (rho h).symm_apply_apply a
    · intro a b c ⟨h, hb⟩ ⟨k, hc⟩
      refine ⟨k * h, ?_⟩
      calc
        rho (k * h) a = rho k (rho h a) := by
          rw [map_mul]
          rfl
        _ = rho k b := congrArg (rho k) hb
        _ = c := hc

/-- Any finite H-set with an H-equivariant involution on its
directed edge indices has an invariant raw-colour lift provided
the effective fibre at every H-orbit reversed by tau contains
an actually self-reversing raw colour. -/
theorem exists_groupInvariantRawOrbitColour
    [Finite A]
    (d : RawDatum G C)
    (rho : H →* Equiv.Perm A)
    (tau : A → A) (htau : Function.Involutive tau)
    (htauCommute : ∀ (h : H) (a : A),
      tau (rho h a) = rho h (tau a))
    (f : A → G)
    (hfInvariant : ∀ (h : H) (a : A), f (rho h a) = f a)
    (hfReverse : ∀ a, f (tau a) = d.s (f a))
    (hSafe : ∀ a, (∃ h : H, rho h a = tau a) →
      ∃ c : C, d.phi c = f a ∧ d.reverse c = c) :
    ∃ colour : A → C,
      (∀ a, d.phi (colour a) = f a) ∧
      (∀ a, colour (tau a) = d.reverse (colour a)) ∧
      (∀ (h : H) (a : A), colour (rho h a) = colour a) := by
  classical
  let E : Setoid A := permOrbitSetoid rho
  let Q := Quotient E
  have hsurj : Function.Surjective (Quotient.mk E : A → Q) := by
    intro q
    induction q using Quotient.inductionOn with
    | _ a => exact ⟨a, rfl⟩
  letI : Finite Q := Finite.of_surjective (Quotient.mk E) hsurj
  let tauQ : Q → Q :=
    Quotient.lift (fun a : A => Quotient.mk E (tau a)) (by
      intro a b hab
      obtain ⟨h, hb⟩ := hab
      apply Quotient.sound
      refine ⟨h, ?_⟩
      calc
        rho h (tau a) = tau (rho h a) :=
          (htauCommute h a).symm
        _ = tau b := congrArg tau hb)
  have htauQ : Function.Involutive tauQ := by
    intro q
    induction q using Quotient.inductionOn with
    | _ a =>
      change Quotient.mk E (tau (tau a)) = Quotient.mk E a
      rw [htau a]
  let fQ : Q → G := Quotient.lift f (by
    intro a b hab
    obtain ⟨h, hb⟩ := hab
    calc
      f a = f (rho h a) := (hfInvariant h a).symm
      _ = f b := congrArg f hb)
  have hfQ : ∀ q : Q, fQ (tauQ q) = d.s (fQ q) := by
    intro q
    induction q using Quotient.inductionOn with
    | _ a =>
      change f (tau a) = d.s (f a)
      exact hfReverse a
  have hfixed : ∀ q : Q, tauQ q = q →
      ∃ c : C, d.phi c = fQ q ∧ d.reverse c = c := by
    intro q hq
    induction q using Quotient.inductionOn with
    | _ a =>
      change Quotient.mk E (tau a) = Quotient.mk E a at hq
      have hrel : E.r a (tau a) := Quotient.exact hq.symm
      exact hSafe a hrel
  obtain ⟨colourQ, hphi, hreverse⟩ :=
    exists_finiteRawColour_of_involutiveOrbits
      d tauQ htauQ fQ hfQ hfixed
  refine ⟨fun a => colourQ (Quotient.mk E a), ?_, ?_, ?_⟩
  · intro a
    exact hphi (Quotient.mk E a)
  · intro a
    exact hreverse (Quotient.mk E a)
  · intro h a
    have heq : Quotient.mk E a =
        Quotient.mk E (rho h a) :=
      Quotient.sound ⟨h, rfl⟩
    exact congrArg colourQ heq.symm

end SemigenericEPPA
