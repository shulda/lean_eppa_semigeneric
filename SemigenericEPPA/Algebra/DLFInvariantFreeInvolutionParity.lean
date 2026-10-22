import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic.Ring

/-!
# Invariant F₂ chains on a free involution have zero augmentation

A parity argument in the relative involution-killing group cover
uses the fact that an F₂-valued chain invariant under a free
order-two edge permutation is constant on two-element orbits.
Consequently its total edge coefficient sum is zero.

We give a direct proof using a linear-order choice of one element
of every two-element orbit: h(e)=f(e) if e<t(e), else zero.
Every value f(e) is h(e)+h(t(e)), and the second sum is a
permutation of the first. Characteristic two finishes the proof.

The result is independent of the concrete relative-cover graph,
quotient graphs, algebraic normality, or any basepoint. Subsequent
parity arguments can combine this lemma with a vertex-orbit
transversal and endpoint equivariance, avoiding an implicit
choice of quotient multigraph.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u
variable {E : Type u} [Fintype E] [LinearOrder E]

private theorem zmodTwo_double (x : ZMod 2) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc
    x + x = (2 : ZMod 2) * x := by ring
    _ = 0 := by rw [h2]; simp

/-- For any free involution of a finite type, every invariant
F₂-valued function has even (zero-mod-two) total sum. -/
theorem sum_invariant_freeInvolution_zero
    (t : Equiv.Perm E)
    (ht : ∀ e : E, t (t e) = e)
    (hfree : ∀ e : E, t e ≠ e)
    (f : E → ZMod 2)
    (hInvariant : ∀ e : E, f (t e) = f e) :
    (∑ e : E, f e) = 0 := by
  classical
  let half : E → ZMod 2 :=
    fun e => if e < t e then f e else 0
  have hSplit (e : E) : f e = half e + half (t e) := by
    by_cases he : e < t e
    · have hre : ¬t e < e := by
        exact not_lt.mpr (le_of_lt he)
      have hhalf : half e = f e := by simp [half, he]
      have hother : half (t e) = 0 := by
        simp [half, ht e, hre]
      rw [hhalf, hother]
      simp
    · have htle : t e < e :=
        lt_of_le_of_ne (le_of_not_gt he) (hfree e)
      have hhalf : half e = 0 := by simp [half, he]
      have hother : half (t e) = f (t e) := by
        simp [half, ht e, htle]
      rw [hhalf, hother, hInvariant e]
      simp
  calc
    (∑ e : E, f e) =
        ∑ e : E, (half e + half (t e)) := by
      apply Finset.sum_congr rfl
      intro e _
      exact hSplit e
    _ = (∑ e : E, half e) + (∑ e : E, half (t e)) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ e : E, half e) + (∑ e : E, half e) := by
      rw [Equiv.sum_comp t half]
    _ = 0 := zmodTwo_double _

end RelativeDLF
end SemigenericEPPA
