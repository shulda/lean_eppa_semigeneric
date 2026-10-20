import SemigenericEPPA.Structure.ThreePlusOneRawObstruction
import SemigenericEPPA.Bridge.RawTypedEPPA
import AllThoseEPPA.PartialIso

/-!
# Exact typed partial involution on the tripleton old E-part

The no-good-colour 3+1 raw obstruction has original vertices
v | a,b,c. The partial automorphism tau has exact source
S={a,b,c}, interchanges a,b and fixes c. It is independent
of all three cross-part raw colours: the induced structure
on S has only one E-part, with no raw cross edges.

We construct tau as a genuine original-language
AllThoseEPPA.Structure.PartialAutomorphism, not as a full old
automorphism. Its source and target are exactly S, its language
action is 1 and its square is the identity on S. Coherence
therefore forces its whole-witness extension to square to 1.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

/-- Swap a and b; fix c and the fourth vertex v OFF the
partial automorphism's domain. -/
def threePlusOneSwap : Option (Option Bool) → Option (Option Bool)
  | none => none
  | some none => some (some false)
  | some (some false) => some none
  | some (some true) => some (some true)

/-- The exact source/range of the partial involution: the entire
tripleton E-part, excluding the singleton old vertex v. -/
def threePlusOneSwapSource : Set (Option (Option Bool)) :=
  {x | x ≠ none}

theorem threePlusOneSwap_involutive
    (x : Option (Option Bool)) :
    threePlusOneSwap (threePlusOneSwap x) = x := by
  cases x with
  | none => rfl
  | some t =>
      cases t with
      | none => rfl
      | some b => cases b <;> rfl

theorem threePlusOneSwap_source
    (x : Option (Option Bool)) (hx : x ∈ threePlusOneSwapSource) :
    threePlusOneSwap x ∈ threePlusOneSwapSource := by
  cases x with
  | none =>
      exact False.elim (hx rfl)
  | some t =>
      cases t with
      | none => simp [threePlusOneSwap, threePlusOneSwapSource]
      | some b =>
          cases b <;>
            simp [threePlusOneSwap, threePlusOneSwapSource]

/-- The partial involution literally preserves the distinguished
E relation on its old domain; in fact it preserves E globally. -/
theorem threePlusOneSwap_part
    (d : RawDatum G C) (col : Option Bool → C)
    (x y : Option (Option Bool)) :
    (d.threePlusOneRawPresentation col).part
        (threePlusOneSwap x) (threePlusOneSwap y) ↔
      (d.threePlusOneRawPresentation col).part x y := by
  have hsome (z : Option (Option Bool)) :
      (threePlusOneSwap z).isSome = z.isSome := by
    cases z with
    | none => rfl
    | some t =>
        cases t with
        | none => rfl
        | some b => cases b <;> rfl
  change (threePlusOneSwap x).isSome =
      (threePlusOneSwap y).isSome ↔ x.isSome = y.isSome
  rw [hsome x, hsome y]

/-- Every old pair from the tripleton source has the absent raw
colour None both before and after tau. No extra colour
hypothesis is ever needed for the partial transposition. -/
theorem threePlusOneSwap_colour
    (d : RawDatum G C) (col : Option Bool → C)
    (x y : Option (Option Bool))
    (hx : x ∈ threePlusOneSwapSource)
    (hy : y ∈ threePlusOneSwapSource) :
    (d.threePlusOneRawPresentation col).colour
        (threePlusOneSwap x) (threePlusOneSwap y) =
      (d.threePlusOneRawPresentation col).colour x y := by
  let P := d.threePlusOneRawPresentation col
  have same (r s : Option (Option Bool))
      (hr : r ∈ threePlusOneSwapSource)
      (hs : s ∈ threePlusOneSwapSource) :
      P.part r s := by
    cases r with
    | none => exact False.elim (hr rfl)
    | some a =>
        cases s with
        | none => exact False.elim (hs rfl)
        | some b => rfl
  have htX := threePlusOneSwap_source x hx
  have htY := threePlusOneSwap_source y hy
  calc
    P.colour (threePlusOneSwap x) (threePlusOneSwap y) =
        none :=
      (P.colour_none_iff _ _).mpr (same _ _ htX htY)
    _ = P.colour x y :=
      ((P.colour_none_iff _ _).mpr (same _ _ hx hy)).symm

/-- Literal exact partial equivalence with source and target
the three-vertex old E-part. -/
def threePlusOnePartialEquiv :
    PartialEquiv (Option (Option Bool)) (Option (Option Bool)) where
  toFun := threePlusOneSwap
  invFun := threePlusOneSwap
  source := threePlusOneSwapSource
  target := threePlusOneSwapSource
  map_source' := threePlusOneSwap_source
  map_target' := threePlusOneSwap_source
  left_inv' := by intro x hx; exact threePlusOneSwap_involutive x
  right_inv' := by intro x hx; exact threePlusOneSwap_involutive x

/-- This exact partial involution is an ACTUAL partial automorphism
of the original four-vertex raw R1--R3 structure, in the upstream
typed original language, irrespective of its three raw colours. -/
noncomputable def RawDatum.threePlusOneTypedTransposition
    (d : RawDatum G C) (col : Option Bool → C) :
    Structure.PartialAutomorphism (rectangleTrivialAction C)
      (d.threePlusOneRawPresentation col).toStructure where
  lang := 1
  toPartialEquiv := threePlusOnePartialEquiv
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
        change (d.threePlusOneRawPresentation col).part
            (threePlusOneSwap (xs 0)) (threePlusOneSwap (xs 1)) ↔
          (d.threePlusOneRawPresentation col).part
            (xs 0) (xs 1)
        exact threePlusOneSwap_part d col (xs 0) (xs 1)
    | some raw =>
        change (d.threePlusOneRawPresentation col).colour
            (threePlusOneSwap (xs 0)) (threePlusOneSwap (xs 1)) =
            some raw ↔
          (d.threePlusOneRawPresentation col).colour
            (xs 0) (xs 1) = some raw
        rw [threePlusOneSwap_colour d col
          (xs 0) (xs 1) (hxs 0) (hxs 1)]
  map_func := by
    intro n F xs hx
    exact PEmpty.elim F

/-- In the exact old tripleton source, tau²=identity, its
language action also squares to 1, and the three old vertices
are interchanged/fixed as required. -/
theorem RawDatum.threePlusOneTypedTransposition_exactSquare
    (d : RawDatum G C) (col : Option Bool → C) :
    let p := d.threePlusOneTypedTransposition col
    p.source = threePlusOneSwapSource ∧
    p.target = threePlusOneSwapSource ∧
    p.lang * p.lang = 1 ∧
    (∀ x : Option (Option Bool),
      x ∈ threePlusOneSwapSource → p (p x) = x) := by
  refine ⟨rfl, rfl, by simp [threePlusOneTypedTransposition], ?_⟩
  intro x hx
  exact threePlusOneSwap_involutive x

end SemigenericEPPA
