import SemigenericEPPA.Algebra.EffectiveGroupGaugeCocycles
import Mathlib.Tactic.Group

/-!
# Explicit reference gauge for occupied and unoccupied old E-indices

In the positive coherent nontrivial-G construction H acts only on an
old selected induced subset S, whereas its label and index actions
are extended to auxiliary old real-label and quotient sorts.

For every target old class index j:
* if S meets j, set z(y,j)=1 for ALL old real labels y;
* if S misses j, set z(y,j)=a(y,j) for y in S and 1 elsewhere.

The reference coboundary
  L^h(x,j)=z(hx,hj)^(-1)*z(x,j)
then has precisely the two properties required by the genuine
witness H-action: it is 1 in every occupied source column, and
on an unoccupied target column j it compensates the difference
between a(x,j) and a(hx,hj). These statements hold with the
original noncommutative multiplication order and do NOT assume
preservation of colours involving old vertices outside S.

On occupied targets, the given old occupied-pair multipliers supply
the remaining old-row transport. On unoccupied targets the neutral
multiplier 1 and the explicit reference twist do the job.

This proves the reference selection for a selected subset S.
It does not supply the occupied multiplier family itself, the
finite padded old action, or its raw-cover lift.
-/

namespace SemigenericEPPA

universe u v w t

variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {V : Type w} {I : Type t}

/-- An old class index visited by the distinguished subset S. -/
def visitedGaugeIndex (S : Set V) (cls : V → I) (j : I) : Prop :=
  ∃ x : V, x ∈ S ∧ cls x = j

/-- One canonical reference gauge chosen from S and all original old
gauge rows a(x,j), BEFORE selecting any H-action on S. -/
noncomputable def selectedReferenceGauge
    (S : Set V) (cls : V → I) (a : V → I → G)
    (y : V) (j : I) : G := by
  classical
  exact if visitedGaugeIndex S cls j then 1
    else if y ∈ S then a y j else 1

theorem selectedReferenceGauge_visited
    (S : Set V) (cls : V → I) (a : V → I → G)
    (y : V) (j : I)
    (hj : visitedGaugeIndex S cls j) :
    selectedReferenceGauge S cls a y j = 1 := by
  simp [selectedReferenceGauge, hj]

theorem selectedReferenceGauge_unvisited_old
    (S : Set V) (cls : V → I) (a : V → I → G)
    (y : V) (j : I)
    (hj : ¬visitedGaugeIndex S cls j)
    (hy : y ∈ S) :
    selectedReferenceGauge S cls a y j = a y j := by
  simp [selectedReferenceGauge, hj, hy]

/-- Genuine H-actions on S and its class labels preserve exactly
the set of visited indices, even if rho does NOT act by effective
automorphisms on any ambient old vertices outside S. -/
theorem visitedGaugeIndex_equivariant
    (S : Set V) (cls : V → I)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (hS : ∀ (h : H) (x : V),
      x ∈ S ↔ rho h x ∈ S)
    (hcls : ∀ (h : H) (x : V),
      cls (rho h x) = iota h (cls x))
    (h : H) (j : I) :
    visitedGaugeIndex S cls (iota h j) ↔
      visitedGaugeIndex S cls j := by
  constructor
  · rintro ⟨y, hy, hyj⟩
    let x : V := (rho h).symm y
    have hx : x ∈ S := by
      apply (hS h x).mpr
      change rho h ((rho h).symm y) ∈ S
      simpa using hy
    have hlabel : cls x = j := by
      have heq := hcls h x
      change cls (rho h ((rho h).symm y)) =
        iota h (cls ((rho h).symm y)) at heq
      rw [(rho h).apply_symm_apply] at heq
      exact (iota h).injective (heq.symm.trans hyj)
    exact ⟨x, hx, hlabel⟩
  · rintro ⟨x, hx, hxj⟩
    refine ⟨rho h x, (hS h x).mp hx, ?_⟩
    rw [hcls h x, hxj]

/-- All reference twists in an occupied SOURCE class are literally
trivial, including on labels outside the selected old subset. This
is exactly what keeps the distinguished source witness part neutral. -/
theorem selectedReferenceGauge_visited_source
    (S : Set V) (cls : V → I) (a : V → I → G)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (hS : ∀ (h : H) (x : V),
      x ∈ S ↔ rho h x ∈ S)
    (hcls : ∀ (h : H) (x : V),
      cls (rho h x) = iota h (cls x))
    (h : H) (x y : V) (hx : x ∈ S) :
    selectedReferenceGauge S cls a (rho h y) (iota h (cls x)) =
      selectedReferenceGauge S cls a y (cls x) := by
  have hi : visitedGaugeIndex S cls (cls x) := ⟨x, hx, rfl⟩
  have hi' : visitedGaugeIndex S cls (iota h (cls x)) :=
    (visitedGaugeIndex_equivariant S cls rho iota hS hcls h (cls x)).mpr hi
  rw [selectedReferenceGauge_visited S cls a (rho h y)
      (iota h (cls x)) hi',
    selectedReferenceGauge_visited S cls a y (cls x) hi]

/-- One selected reference z simultaneously supplies every old-row
correction: for occupied j use the genuine transported gauge row;
for unoccupied j use the neutral multiplier and the coboundary
z(hx,hj)^(-1) z(x,j). Neither step assumes S meets every class. -/
theorem selectedReferenceGauge_old_row
    (S : Set V) (cls : V → I) (a : V → I → G)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (hS : ∀ (h : H) (x : V),
      x ∈ S ↔ rho h x ∈ S)
    (hcls : ∀ (h : H) (x : V),
      cls (rho h x) = iota h (cls x))
    (M : H → I → I → G)
    (hOccRow : ∀ (h : H) (x : V), x ∈ S →
      ∀ (j : I), visitedGaugeIndex S cls j →
        M h (cls x) j * a x j =
          a (rho h x) (iota h j))
    (hUnused : ∀ (h : H) (i j : I),
      ¬visitedGaugeIndex S cls j → M h i j = 1)
    (h : H) (x : V) (hx : x ∈ S) (j : I) :
    M h (cls x) j * a x j =
      a (rho h x) (iota h j) *
        referenceGaugeTwist rho iota
          (selectedReferenceGauge S cls a) h x j := by
  by_cases hj : visitedGaugeIndex S cls j
  · have hj' : visitedGaugeIndex S cls (iota h j) :=
      (visitedGaugeIndex_equivariant S cls rho iota hS hcls h j).mpr hj
    have htwist : referenceGaugeTwist rho iota
        (selectedReferenceGauge S cls a) h x j = 1 := by
      unfold referenceGaugeTwist
      rw [selectedReferenceGauge_visited S cls a (rho h x)
            (iota h j) hj',
          selectedReferenceGauge_visited S cls a x j hj]
      group
    rw [htwist, mul_one]
    exact hOccRow h x hx j hj
  · have hj' : ¬visitedGaugeIndex S cls (iota h j) := by
      intro hj'
      exact hj ((visitedGaugeIndex_equivariant
        S cls rho iota hS hcls h j).mp hj')
    have hrx : rho h x ∈ S := (hS h x).mp hx
    have hM : M h (cls x) j = 1 := hUnused h (cls x) j hj
    rw [hM, one_mul]
    unfold referenceGaugeTwist
    rw [selectedReferenceGauge_unvisited_old
          S cls a (rho h x) (iota h j) hj' hrx,
        selectedReferenceGauge_unvisited_old
          S cls a x j hj hx]
    group

end SemigenericEPPA
