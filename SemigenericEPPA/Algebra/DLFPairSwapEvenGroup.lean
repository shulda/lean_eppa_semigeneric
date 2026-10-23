import Mathlib.GroupTheory.FixedPointFree

/-!
# Two-cycle in a finite group action forces an involution in the group

The final negative DLF parity argument requires NO assumption that
the extension of a partial two-point transposition has order two:
a finite-group action element k which swaps x,y in both directions
can have higher even order. Its odd powers still swap x,y, so the
order of k cannot be odd.

Lagrange then forces the order of the finite acting group to be
even, and Cauchy's theorem supplies some nonidentity involution
in that group. This abstracts the only group-theoretic part of
the negative semi-coherent DLF cofinality contradiction.

No faithful action is needed, and no topological or rectangle
hypotheses are involved.
-/

namespace SemigenericEPPA

universe u v
variable {H : Type u} [Group H] [Finite H]
variable {V : Type v}

/-- Every odd positive power of a permutation exchanging a distinct
pair x,y again sends x to y. Other cycles of the permutation may
be arbitrary. -/
theorem oddPower_sends_swappedPair
    (f : Equiv.Perm V) (x y : V)
    (hxy : f x = y) (hyx : f y = x) :
    ∀ n : ℕ, (f ^ (2 * n + 1)) x = y := by
  intro n
  induction n with
  | zero =>
      simpa only [mul_zero, zero_add, pow_one] using hxy
  | succ n ih =>
      have hs : 2 * (n + 1) + 1 = 2 + (2 * n + 1) := by
        simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      calc
        (f ^ (2 * (n + 1) + 1)) x =
            (f ^ (2 + (2 * n + 1))) x := by rw [hs]
        _ = (f ^ 2) ((f ^ (2 * n + 1)) x) := by
          rw [pow_add, Equiv.Perm.mul_apply]
        _ = y := by
          rw [ih]
          simp only [pow_two, Equiv.Perm.mul_apply, hyx, hxy]

/-- A finite group of odd cardinality cannot contain ANY action
element swapping two distinct points in both directions. The
argument applies even to non-faithful and non-transitive actions. -/
theorem oddFiniteGroup_no_swappedPair
    (rho : H →* Equiv.Perm V)
    (hOdd : Odd (Nat.card H))
    (h : H) (x y : V)
    (hxy : rho h x = y) (hyx : rho h y = x)
    (hneq : x ≠ y) :
    False := by
  have hOddOrder : Odd (orderOf h) :=
    Odd.of_dvd_nat hOdd (orderOf_dvd_natCard h)
  obtain ⟨n, hn⟩ := hOddOrder
  have hPowOne : (rho h) ^ (orderOf h) = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hFix : ((rho h) ^ (orderOf h)) x = x := by
    rw [hPowOne]
    rfl
  have hMove : ((rho h) ^ (orderOf h)) x = y := by
    rw [hn]
    exact oddPower_sends_swappedPair (rho h) x y hxy hyx n
  exact hneq (hFix.symm.trans hMove)

/-- If a finite group action contains a two-cycle, then
the finite group has even cardinality. -/
theorem even_natCard_of_swappedPair
    (rho : H →* Equiv.Perm V)
    (h : H) (x y : V)
    (hxy : rho h x = y) (hyx : rho h y = x)
    (hneq : x ≠ y) :
    Even (Nat.card H) := by
  by_contra hNotEven
  exact oddFiniteGroup_no_swappedPair rho
    (Nat.not_even_iff_odd.mp hNotEven)
    h x y hxy hyx hneq

/-- Cauchy's theorem applied AFTER showing even cardinality:
there must be a nonidentity element of square one in the finite
acting group. This is a genuine group involution, even if the
original element swapping the two points had order larger than 2. -/
theorem exists_nontrivial_involution_of_swappedPair
    (rho : H →* Equiv.Perm V)
    (h : H) (x y : V)
    (hxy : rho h x = y) (hyx : rho h y = x)
    (hneq : x ≠ y) :
    ∃ a : H, a ≠ 1 ∧ a * a = 1 := by
  have heven : 2 ∣ Nat.card H :=
    (even_iff_two_dvd).mp
      (even_natCard_of_swappedPair rho h x y hxy hyx hneq)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card 2 heven
  refine ⟨a, ?_, ?_⟩
  · intro hOne
    rw [hOne, orderOf_one] at ha
    simp at ha
  · have hPow := pow_orderOf_eq_one a
    rw [ha] at hPow
    simpa only [pow_two] using hPow

end SemigenericEPPA
