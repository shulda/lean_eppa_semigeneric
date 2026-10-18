import SemigenericEPPA.Bridge.CoherentInvolutionForcing

/-!
# The empty-good-colour obstruction to coherent EPPA

When no effective fibre contains a self-reversing raw colour, the
three-point old profile used in the manuscript's coherent-EPPA
necessity proof cannot admit an involutive raw automorphism
extending its old transposition.

There are two cases for w=T(v). If w and v lie in different E
parts, the involution swaps the raw ordered pair (v,w), forcing a
self-reversing raw colour. Otherwise v E w, and a rectangle with
columns a,c forces the old effective colour g at (v,a) to be 1,
contrary to its choice g != 1.

This proves the *local obstruction*, including its exact
noncommutative group-valued rectangle calculation and all
raw-reversal conditions. The separate groupoid step must show
that a coherent extension of the old transposition supplies an
actual involution T, and the finite old four-point configuration
must be instantiated as a member of the raw class.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}

/-- The manuscript's empty-good-colour profile is incompatible
with any genuine involutive automorphism extending the old
transposition. No assumption of commutativity or s(1)=1 occurs. -/
theorem RawRectanglePresentation.noGood_involutiveProfile_impossible
    (P : RawRectanglePresentation d V)
    (hEmpty : ∀ g : G, g ∉ d.selfReverseEffective)
    (T : Equiv.Perm V)
    (hTcolour : ∀ x y, P.colour (T x) (T y) = P.colour x y)
    (hT2 : ∀ x, T (T x) = x)
    (a b c v : V)
    (hab : P.part a b)
    (hac : P.part a c)
    (hva : ¬P.part v a)
    (hTb : T b = a)
    (hTc : T c = c)
    (g : G) (hg : g ≠ 1)
    (hvaG : P.effectiveReduct.F v a = g)
    (hvbG : P.effectiveReduct.F v b = 1)
    (hvcG : P.effectiveReduct.F v c = 1) :
    False := by
  let D : EffectiveGeometry d.s V := P.effectiveReduct
  let w : V := T v
  have hTpart (x y : V) :
      P.part (T x) (T y) ↔ P.part x y := by
    calc
      P.part (T x) (T y) ↔ P.colour (T x) (T y) = none :=
        (P.colour_none_iff (T x) (T y)).symm
      _ ↔ P.colour x y = none := by rw [hTcolour x y]
      _ ↔ P.part x y := P.colour_none_iff x y
  have hvb : ¬P.part v b := by
    intro h
    exact hva (P.part_equiv.trans h (P.part_equiv.symm hab))
  have hvc : ¬P.part v c := by
    intro h
    exact hva (P.part_equiv.trans h (P.part_equiv.symm hac))
  have hTEff (x y : V) (hxy : ¬P.part x y) :
      D.F (T x) (T y) = D.F x y := by
    have hcross : ¬P.part (T x) (T y) := by
      intro h
      exact hxy ((hTpart x y).mp h)
    exact P.effectiveReduct_equalColour
      (T x) (T y) x y (hTcolour x y) hcross
  by_cases hvw : P.part v w
  · have hDvw : D.part v w :=
      (P.effectiveReduct_part v w).mpr hvw
    have hDac : D.part a c :=
      (P.effectiveReduct_part a c).mpr hac
    have hDva : ¬D.part v a := by
      intro h
      exact hva ((P.effectiveReduct_part v a).mp h)
    have hFwa : D.F w a = (1 : G) := by
      have heq := hTEff v b hvb
      change D.F w (T b) = D.F v b at heq
      rw [hTb] at heq
      exact heq.trans hvbG
    have hFwc : D.F w c = (1 : G) := by
      have heq := hTEff v c hvc
      change D.F w (T c) = D.F v c at heq
      rw [hTc] at heq
      exact heq.trans hvcG
    have hrect := D.rectangle v w a c hDvw hDac hDva
    have hginv : g⁻¹ = (1 : G) := by
      simpa only [hvaG, hvcG, hFwa, hFwc,
        inv_one, mul_one, one_mul] using hrect
    have hg1 : g = (1 : G) := by
      have heq := congrArg (fun x : G => x⁻¹) hginv
      simpa using heq
    exact hg hg1
  · have hwv : T w = v := hT2 v
    obtain ⟨raw, _, hfix⟩ :=
      P.selfReverse_of_swappedPair
        T hTcolour v w hvw rfl hwv
    exact hEmpty (d.phi raw) ⟨raw, rfl, hfix⟩

end SemigenericEPPA
