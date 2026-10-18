import Mathlib.Order.Basic

/-!
# Equivariant retraction that also preserves a fibre index

A set A and an embedded set B carry involutions rA,rB as well as
maps pA:A→I, pB:B→I. The index involution s:I→I is respected by
both reversals. If e:B→A is an equivariant injection over I and
every fibre of B is inhabited, the inverse on the image of e can
be extended to a fibre-preserving equivariant retraction provided
that fixed points of rA admit fixed targets in the same fibre.

The proof orients each unembedded nonfixed orbit using an auxiliary
linear order on A. The default of an oriented orbit is chosen
in the correct indexed fibre; its partner is obtained by reversal.
This extra fibre-preservation is not supplied by an ordinary
retraction theorem.

We will apply it to A=G×L, B=C, pA(g,l)=g, pB(c)=phi(c),
rA(g,l)=(s(g),shift(g)-l) and rB(c)=c*. Its output is precisely
the global raw decoder needed for AffineResidualCode.
-/

namespace SemigenericEPPA

universe u v w
variable {A : Type u} {B : Type v} {I : Type w}
variable [LinearOrder A]

theorem exists_equivariantFibreRetraction
    (rA : A → A) (hrA : Function.Involutive rA)
    (rB : B → B) (hrB : Function.Involutive rB)
    (s : I → I)
    (pA : A → I) (pB : B → I)
    (hindexA : ∀ a : A, pA (rA a) = s (pA a))
    (hindexB : ∀ b : B, pB (rB b) = s (pB b))
    (e : B → A) (he : Function.Injective e)
    (hequiv : ∀ b : B, e (rB b) = rA (e b))
    (hindexE : ∀ b : B, pA (e b) = pB b)
    (hsurj : Function.Surjective pB)
    (hfixed : ∀ a : A, rA a = a →
      ∃ b : B, pB b = pA a ∧ rB b = b) :
    ∃ q : A → B,
      (∀ b : B, q (e b) = b) ∧
      (∀ a : A, pB (q a) = pA a) ∧
      (∀ a : A, q (rA a) = rB (q a)) := by
  classical
  let default : I → B := fun i => Classical.choose (hsurj i)
  have hdefault (i : I) : pB (default i) = i :=
    Classical.choose_spec (hsurj i)
  let q : A → B := fun a =>
    if h : ∃ b : B, e b = a then Classical.choose h
    else if hf : rA a = a then Classical.choose (hfixed a hf)
    else if a < rA a then default (pA a)
    else rB (default (pA (rA a)))
  have hq_image (b : B) : q (e b) = b := by
    have h : ∃ b' : B, e b' = e b := ⟨b, rfl⟩
    change (if h : ∃ b' : B, e b' = e b then
      Classical.choose h else
      if hf : rA (e b) = e b then Classical.choose (hfixed (e b) hf)
      else if e b < rA (e b) then default (pA (e b))
      else rB (default (pA (rA (e b))))) = b
    rw [dif_pos h]
    exact he (Classical.choose_spec h)
  have hq_index (a : A) : pB (q a) = pA a := by
    by_cases hm : ∃ b : B, e b = a
    · have ha : q a = Classical.choose hm := by
        dsimp [q]
        rw [dif_pos hm]
      rw [ha]
      calc
        pB (Classical.choose hm) =
          pA (e (Classical.choose hm)) :=
            (hindexE (Classical.choose hm)).symm
        _ = pA a := congrArg pA (Classical.choose_spec hm)
    · by_cases hf : rA a = a
      · have ha : q a = Classical.choose (hfixed a hf) := by
          dsimp [q]
          rw [dif_neg hm, dif_pos hf]
        rw [ha]
        exact (Classical.choose_spec (hfixed a hf)).1
      · by_cases hlt : a < rA a
        · have ha : q a = default (pA a) := by
            simp [q, hm, hf, hlt]
          rw [ha]
          exact hdefault (pA a)
        · have ha : q a = rB (default (pA (rA a))) := by
            simp [q, hm, hf, hlt]
          rw [ha, hindexB, hdefault]
          calc
            s (pA (rA a)) = pA (rA (rA a)) :=
              (hindexA (rA a)).symm
            _ = pA a := congrArg pA (hrA a)
  have hq_equiv (a : A) : q (rA a) = rB (q a) := by
    by_cases hm : ∃ b : B, e b = a
    · let b : B := Classical.choose hm
      have hb : e b = a := Classical.choose_spec hm
      calc
        q (rA a) = q (e (rB b)) := by rw [hequiv b, hb]
        _ = rB b := hq_image (rB b)
        _ = rB (q a) := by rw [← hb, hq_image b]
    · have hm' : ¬∃ b : B, e b = rA a := by
        rintro ⟨b, hb⟩
        apply hm
        refine ⟨rB b, ?_⟩
        calc
          e (rB b) = rA (e b) := hequiv b
          _ = rA (rA a) := congrArg rA hb
          _ = a := hrA a
      by_cases hf : rA a = a
      · have ha : q a = Classical.choose (hfixed a hf) := by
          dsimp [q]
          rw [dif_neg hm, dif_pos hf]
        calc
          q (rA a) = q a := congrArg q hf
          _ = rB (q a) := by
            rw [ha]
            exact (Classical.choose_spec (hfixed a hf)).2.symm
      · have hf' : rA (rA a) ≠ rA a := by
          rw [hrA a]
          exact Ne.symm hf
        rcases lt_or_gt_of_ne (Ne.symm hf) with hlt | hgt
        · have hnlt : ¬rA a < a := not_lt_of_ge (le_of_lt hlt)
          have ha : q a = default (pA a) := by
            simp [q, hm, hf, hlt]
          have ha' : q (rA a) = rB (default (pA a)) := by
            simp [q, hm', hf', hrA a, hnlt]
          rw [ha, ha']
        · have hnlt : ¬a < rA a := not_lt_of_ge (le_of_lt hgt)
          have ha : q a = rB (default (pA (rA a))) := by
            simp [q, hm, hf, hnlt]
          have ha' : q (rA a) = default (pA (rA a)) := by
            simp [q, hm', hf', hrA a, hgt]
          rw [ha, ha', hrB]
  exact ⟨q, hq_image, hq_index, hq_equiv⟩

end SemigenericEPPA
