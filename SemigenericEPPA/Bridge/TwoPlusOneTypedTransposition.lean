import SemigenericEPPA.Structure.TwoPlusOneRawObstruction
import SemigenericEPPA.Bridge.RawTypedEPPA
import AllThoseEPPA.PartialIso

/-!
# The exact original partial transposition in the 2+1 raw obstruction

Let P be the three-vertex structure u,v | z constructed from two
arbitrary raw cross-colours, where u=some false, v=some true and
z=none. Suppose only that the first cross-colour c(false) is
self-reversing.

Then the swap u↔z is a literal partial automorphism of P on
the exact two-vertex induced substructure S={u,z}; it fixes the
domain/range S setwise and squares to the identity ON S.

The partial map is constructed in the original AllThoseEPPA typed
language, not merely as a raw permutation. In particular,
its language action is 1, source and target are exactly S, and
the original E and EVERY P_c predicate are preserved.
This is the transposition to which the already Lean-certified
CoherentClosedSubsetInvolution theorem applies.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

/-- The literal map on three old vertices which interchanges
u and z, while leaving the third vertex v fixed off-domain. -/
def twoPlusOneSwap : Option Bool → Option Bool
  | none => some false
  | some false => none
  | some true => some true

def twoPlusOneSwapSource : Set (Option Bool) :=
  {x | x ≠ some true}

@[simp] theorem twoPlusOneSwap_involutive
    (x : Option Bool) : twoPlusOneSwap (twoPlusOneSwap x) = x := by
  cases x with
  | none => rfl
  | some b => cases b <;> rfl

theorem twoPlusOneSwap_source
    (x : Option Bool) (hx : x ∈ twoPlusOneSwapSource) :
    twoPlusOneSwap x ∈ twoPlusOneSwapSource := by
  cases x with
  | none => simp [twoPlusOneSwap, twoPlusOneSwapSource]
  | some b =>
      cases b <;>
        simp_all [twoPlusOneSwap, twoPlusOneSwapSource]

/-- A genuine partial equivalence with exactly the old domain
and range {u,z}, not a larger swap on all three vertices. -/
def twoPlusOnePartialEquiv : PartialEquiv (Option Bool) (Option Bool) where
  toFun := twoPlusOneSwap
  invFun := twoPlusOneSwap
  source := twoPlusOneSwapSource
  target := twoPlusOneSwapSource
  map_source' := twoPlusOneSwap_source
  map_target' := twoPlusOneSwap_source
  left_inv' := by
    intro x hx
    exact twoPlusOneSwap_involutive x
  right_inv' := by
    intro x hx
    exact twoPlusOneSwap_involutive x

/-- Swapping only u,z preserves the exact E partition. -/
theorem twoPlusOneSwap_part
    (d : RawDatum G C) (c : Bool → C)
    (x y : Option Bool)
    (hx : x ∈ twoPlusOneSwapSource)
    (hy : y ∈ twoPlusOneSwapSource) :
    (d.twoPlusOneRawPresentation c).part
      (twoPlusOneSwap x) (twoPlusOneSwap y) ↔
    (d.twoPlusOneRawPresentation c).part x y := by
  cases x with
  | none =>
      cases y with
      | none => simp [twoPlusOneSwap, RawDatum.twoPlusOneRawPresentation]
      | some b => cases b <;>
          simp_all [twoPlusOneSwapSource, twoPlusOneSwap,
            RawDatum.twoPlusOneRawPresentation]
  | some a =>
      cases a <;> cases y with
      | none =>
          simp_all [twoPlusOneSwapSource, twoPlusOneSwap,
            RawDatum.twoPlusOneRawPresentation]
      | some b =>
          cases b <;> simp_all [twoPlusOneSwapSource,
            twoPlusOneSwap, RawDatum.twoPlusOneRawPresentation]

/-- Raw colours (including the within-part value none) are
unchanged by the old transposition precisely when c(false) is
self-reversing; no restriction on c(true) is used. -/
theorem twoPlusOneSwap_colour
    (d : RawDatum G C) (c : Bool → C)
    (hfix : d.reverse (c false) = c false)
    (x y : Option Bool)
    (hx : x ∈ twoPlusOneSwapSource)
    (hy : y ∈ twoPlusOneSwapSource) :
    (d.twoPlusOneRawPresentation c).colour
      (twoPlusOneSwap x) (twoPlusOneSwap y) =
    (d.twoPlusOneRawPresentation c).colour x y := by
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some b => cases b <;>
          simp_all [twoPlusOneSwapSource, twoPlusOneSwap,
            RawDatum.twoPlusOneRawPresentation, hfix]
  | some a =>
      cases a <;> cases y with
      | none =>
          simp_all [twoPlusOneSwapSource, twoPlusOneSwap,
            RawDatum.twoPlusOneRawPresentation, hfix]
      | some b =>
          cases b <;> simp_all [twoPlusOneSwapSource,
            twoPlusOneSwap, RawDatum.twoPlusOneRawPresentation, hfix]

/-- The ACTUAL typed partial automorphism of the old 2+1
raw obstruction, with exact two-vertex support {u,z}. -/
noncomputable def RawDatum.twoPlusOneTypedTransposition
    (d : RawDatum G C) (c : Bool → C)
    (hfix : d.reverse (c false) = c false) :
    Structure.PartialAutomorphism (rectangleTrivialAction C)
      (d.twoPlusOneRawPresentation c).toStructure where
  lang := 1
  toPartialEquiv := twoPlusOnePartialEquiv
  source_closed := by
    intro n F xs hx
    exact PEmpty.elim F
  target_closed := by
    intro n F xs hx
    exact PEmpty.elim F
  map_rel_iff := by
    intro n R xs hxs
    simp only [Language.Action.onRel_one]
    rcases R with ⟨name, hn⟩
    subst n
    cases name with
    | none =>
        change (d.twoPlusOneRawPresentation c).part
            (twoPlusOneSwap (xs 0)) (twoPlusOneSwap (xs 1)) ↔
          (d.twoPlusOneRawPresentation c).part (xs 0) (xs 1)
        exact twoPlusOneSwap_part d c _ _ (hxs 0) (hxs 1)
    | some colour =>
        change (d.twoPlusOneRawPresentation c).colour
            (twoPlusOneSwap (xs 0)) (twoPlusOneSwap (xs 1)) =
              some colour ↔
          (d.twoPlusOneRawPresentation c).colour (xs 0) (xs 1) =
              some colour
        rw [twoPlusOneSwap_colour d c hfix _ _ (hxs 0) (hxs 1)]
  map_func := by
    intro n F xs hxs
    exact PEmpty.elim F

/-- The old partial transposition is a literal involution
on its EXACT source, not a condition about the auxiliary
off-domain total function. -/
theorem RawDatum.twoPlusOneTypedTransposition_exactSquare
    (d : RawDatum G C) (c : Bool → C)
    (hfix : d.reverse (c false) = c false) :
    let p := d.twoPlusOneTypedTransposition c hfix
    p.source = twoPlusOneSwapSource ∧
    p.target = twoPlusOneSwapSource ∧
    p.lang * p.lang = 1 ∧
    (∀ x : Option Bool, x ∈ twoPlusOneSwapSource →
      p (p x) = x) := by
  refine ⟨rfl, rfl, by simp [twoPlusOneTypedTransposition], ?_⟩
  intro x hx
  exact twoPlusOneSwap_involutive x

end SemigenericEPPA
