import SemigenericEPPA.Valuations.TwistedPartPermutation
import Mathlib.Tactic.Group

/-!
# The explicit old partial-map twist (manuscript 3.16–3.17)

For a chosen injection p on a partial old domain, the prescribed
multipliers m(i,j), and a permutation ι of the old part labels, the
function L(x,j) is trivial for already touched target parts j, and
uses the exact (noncommutative) correction
  a(p(x), ι(j))⁻¹ · m(i,j) · a(x,j)
for untouched target parts.

The old coordinate equality holds whenever the chosen multipliers
obey (3.14) on touched target parts. We also substitute this identity
into the *actual permutation of valuation functions* constructed in
TwistedPartPermutation. No finite-group or self-reversal hypothesis
is used; this is an algebraic component of E0, not an EPPA theorem.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {V : Type v} {I : Type w}

/-- The noncommutative correction L_(x,j) from (3.16).
It is 1 for every visited target part, whether or not x is in the
partial domain; for an unvisited j it is also 1 outside that domain. -/
noncomputable def oldPartialGaugeTwist
    (S : Set V) (p : S → V)
    (ι : Equiv.Perm I) (P : I → Prop)
    (cls : V → I) (a : V → I → G) (m : I → I → G)
    (j : I) (x : V) : G := by
  classical
  exact if P j then 1
    else if hx : x ∈ S then
      (a (p ⟨x, hx⟩) (ι j))⁻¹ * m (cls x) j * a x j
    else 1

/-- The twist is trivial on every visited target part (3.16). -/
theorem oldPartialGaugeTwist_visited
    (S : Set V) (p : S → V)
    (ι : Equiv.Perm I) (P : I → Prop)
    (cls : V → I) (a : V → I → G) (m : I → I → G)
    (j : I) (hj : P j) (x : V) :
    oldPartialGaugeTwist S p ι P cls a m j x = 1 := by
  classical
  simp [oldPartialGaugeTwist, hj]

/-- For an old partial-domain vertex, compute the untouched-target
twist literally, retaining the multiplication order (3.16). -/
theorem oldPartialGaugeTwist_unvisited
    (S : Set V) (p : S → V)
    (ι : Equiv.Perm I) (P : I → Prop)
    (cls : V → I) (a : V → I → G) (m : I → I → G)
    (j : I) (hj : ¬P j) (x : S) :
    oldPartialGaugeTwist S p ι P cls a m j x.val =
      (a (p x) (ι j))⁻¹ * m (cls x.val) j * a x.val j := by
  classical
  simp [oldPartialGaugeTwist, hj, x.property]

/-- All old target incidences have the required transport formula.
The input is precisely (3.14) on the visited target parts; the
formula for unvisited parts follows from the definition of L. -/
theorem oldPartialGaugeTwist_incidence
    (S : Set V) (p : S → V)
    (ι : Equiv.Perm I) (P : I → Prop)
    (cls : V → I) (a : V → I → G) (m : I → I → G)
    (hvisited : ∀ (x : S) (j : I), P j →
      m (cls x.val) j * a x.val j = a (p x) (ι j))
    (x : S) (j : I) :
    a (p x) (ι j) *
        oldPartialGaugeTwist S p ι P cls a m j x.val =
      m (cls x.val) j * a x.val j := by
  by_cases hj : P j
  · rw [oldPartialGaugeTwist_visited S p ι P cls a m j hj x.val, mul_one]
    exact (hvisited x j hj).symm
  · rw [oldPartialGaugeTwist_unvisited S p ι P cls a m j hj x]
    group

/-- With the *actual* twisted permutation on G-valued valuations,
the old incidence multiplied by the target old gauge equals exactly
the prescribed multiplier times the original incidence. This is the
coordinate equality needed at the end of (3.19). -/
theorem oldPartialGaugeTwist_targetIncidence
    (S : Set V) (p : S → V)
    (ι : Equiv.Perm I) (P : I → Prop)
    (cls : V → I) (a : V → I → G) (m : I → I → G)
    (hvisited : ∀ (x : S) (j : I), P j →
      m (cls x.val) j * a x.val j = a (p x) (ι j))
    (π : Equiv.Perm V) (h : V → G) (x : S) (j : I) :
    a (p x) (ι j) *
      (twistPartValuation π (oldPartialGaugeTwist S p ι P cls a m j) h) (π x.val) =
      m (cls x.val) j * (a x.val j * h x.val) := by
  rw [twistPartValuation_apply_at]
  calc
    a (p x) (ι j) *
      (oldPartialGaugeTwist S p ι P cls a m j x.val * h x.val) =
        (a (p x) (ι j) *
          oldPartialGaugeTwist S p ι P cls a m j x.val) * h x.val := by group
    _ = (m (cls x.val) j * a x.val j) * h x.val := by
      rw [oldPartialGaugeTwist_incidence S p ι P cls a m hvisited x j]
    _ = m (cls x.val) j * (a x.val j * h x.val) := by group

end SemigenericEPPA
