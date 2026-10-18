import Mathlib.Order.Basic
import Mathlib.Logic.Function.Basic

/-!
# Equivariant retractions of involutive sets

Let A and B carry involutions rA and rB, and suppose B embeds
equivariantly into A. The embedding extends to a retraction
q : A -> B that remains equivariant, provided that a fixed point
in A forces the existence of a fixed point in B.

No finiteness hypothesis is needed when A has an auxiliary linear
order. On each unembedded nonfixed orbit {a,rA(a)}, choose a
canonical orientation and send it to a fixed default b0 and its
reverse. An unembedded fixed point is sent to one globally chosen
fixed point of B.

This is the elementary orbit argument needed for the finite affine
residual-code decoder. The auxiliary order is not retained in
the decoded raw language.
-/

namespace SemigenericEPPA

universe u v

variable {A : Type u} {B : Type v}
variable [LinearOrder A] [Nonempty B]

/-- A fixed point in an involutive source can be decoded
equivariantly only if the target involution has a fixed point. -/
theorem exists_equivariantInvolutionRetraction
    (rA : A → A) (hrA : Function.Involutive rA)
    (rB : B → B) (hrB : Function.Involutive rB)
    (e : B → A) (he : Function.Injective e)
    (hequiv : ∀ b : B, e (rB b) = rA (e b))
    (hfixed : (∃ a : A, rA a = a) → ∃ b : B, rB b = b) :
    ∃ q : A → B,
      (∀ b : B, q (e b) = b) ∧
      (∀ a : A, q (rA a) = rB (q a)) := by
  classical
  let b₀ : B := Classical.choice inferInstance
  let fixedB : B := if h : ∃ a : A, rA a = a
    then Classical.choose (hfixed h) else b₀
  have hfixedB (a : A) (ha : rA a = a) :
      rB fixedB = fixedB := by
    have h : ∃ a : A, rA a = a := ⟨a, ha⟩
    simpa [fixedB, h] using
      (Classical.choose_spec (hfixed h))
  let q : A → B := fun a =>
    if h : ∃ b : B, e b = a then Classical.choose h
    else if rA a = a then fixedB
    else if a < rA a then b₀ else rB b₀
  have hq (b : B) : q (e b) = b := by
    have h : ∃ z : B, e z = e b := ⟨b, rfl⟩
    change (if h : ∃ z : B, e z = e b then Classical.choose h
      else if rA (e b) = e b then fixedB
      else if e b < rA (e b) then b₀ else rB b₀) = b
    rw [dif_pos h]
    exact he (Classical.choose_spec h)
  refine ⟨q, hq, ?_⟩
  intro a
  by_cases ha : ∃ b : B, e b = a
  · let b : B := Classical.choose ha
    have hb : e b = a := Classical.choose_spec ha
    calc
      q (rA a) = q (e (rB b)) := by rw [hequiv b, hb]
      _ = rB b := hq (rB b)
      _ = rB (q a) := by rw [← hb, hq b]
  · have ha' : ¬∃ b : B, e b = rA a := by
      rintro ⟨b, hb⟩
      apply ha
      refine ⟨rB b, ?_⟩
      calc
        e (rB b) = rA (e b) := hequiv b
        _ = rA (rA a) := congrArg rA hb
        _ = a := hrA a
    by_cases hfixA : rA a = a
    · have hfixA' : rA (rA a) = rA a := by
        rw [hrA a, hfixA]
      have ha1 : q a = fixedB := by
        simp [q, ha, hfixA]
      have ha2 : q (rA a) = fixedB := by
        simp [q, ha', hfixA']
      rw [ha1, ha2, hfixedB a hfixA]
    · have hfixA' : rA (rA a) ≠ rA a := by
        rw [hrA a]
        exact Ne.symm hfixA
      rcases lt_or_gt_of_ne (Ne.symm hfixA) with hlt | hgt
      · have hnlt : ¬rA a < a :=
          not_lt_of_ge (le_of_lt hlt)
        have ha1 : q a = b₀ := by
          simp [q, ha, hfixA, hlt]
        have ha2 : q (rA a) = rB b₀ := by
          simp [q, ha', hfixA', hrA a, hnlt]
        rw [ha1, ha2]
      · have hnlt : ¬a < rA a :=
          not_lt_of_ge (le_of_lt hgt)
        have ha1 : q a = rB b₀ := by
          simp [q, ha, hfixA, hnlt]
        have ha2 : q (rA a) = b₀ := by
          simp [q, ha', hfixA', hrA a, hgt]
        rw [ha1, ha2, hrB b₀]

end SemigenericEPPA
