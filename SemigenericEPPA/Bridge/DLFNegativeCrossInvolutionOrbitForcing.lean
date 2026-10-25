import SemigenericEPPA.Bridge.CoherentOrbitSwappedPair
import SemigenericEPPA.Bridge.DLFDeltaProfileMovingThirdPoint
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport

/-!
# A global cross-class involution swap forces one complete good orbit

The relative/negative DLF argument can be decoupled into two
independent mechanisms.

If an actual raw automorphism T of square one swaps an E-cross
pair x,y, then the raw colour of (x,y) is genuinely fixed by raw
reversal, hence its effective value g is good.

Suppose further that for EVERY affine parameter a:G, one can find
v E x having effective colour F(v,y)=a*g. The involution maps v to
T(v) E y. Raw invariance and reversal force
F(x,T(v))=s(a*g), and the certified coherent orbit rectangle
forces congruence(s,a,g) to have a self-reversing raw lift.

Thus a single cross-E involution swap plus arbitrary row
realizability already forces a COMPLETE good orbit.

For a homogeneous full-age Fraisse limit the missing bridge is the
relative finite row-extension existence theorem. This module
deliberately keeps that precise geometric hypothesis visible; it
does NOT assume arbitrary homogeneous models satisfy it.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- A literal order-two raw automorphism interchanging vertices
from different E-classes forces the entire affine congruence orbit
of their effective colour to be good, provided every left
multiplier can be realized by an extra point in the first class. -/
theorem completeGoodOrbitAt_of_crossInvolution_and_rowRealization
    (P : RawRectanglePresentation d V)
    (T : Equiv.Perm V)
    (hTcolour : ∀ x y : V,
      P.colour (T x) (T y) = P.colour x y)
    (hTtwo : ∀ z : V, T (T z) = z)
    (x y : V)
    (hcross : ¬P.part x y)
    (hTx : T x = y)
    (hTy : T y = x)
    (hRows : ∀ a : G,
      ∃ z : V, P.part x z ∧
        P.effectiveReduct.F z y =
          a * P.effectiveReduct.F x y) :
    d.GoodCompleteOrbitAt (P.effectiveReduct.F x y) := by
  classical
  let g : G := P.effectiveReduct.F x y
  obtain ⟨c, hc, hFix⟩ :=
    P.selfReverse_of_swappedPair T hTcolour x y hcross hTx hTy
  have hGood : g ∈ d.selfReverseEffective :=
    ⟨c, P.effectiveReduct_crossColour x y c hc, hFix⟩
  have hgFixed : d.s g = g :=
    d.selfReverseEffective_subset_fixed hGood
  intro a
  obtain ⟨z, hxz, hzy⟩ := hRows a
  have hyTz : P.part y (T z) := by
    have h :=
      (P.part_iff_of_colourEquivariant T hTcolour x z).mpr hxz
    simpa only [hTx] using h
  have hxTz : ¬P.part x (T z) := by
    intro h
    exact hcross (P.part_equiv.trans h (P.part_equiv.symm hyTz))
  have hzyCross : ¬P.part z y := by
    intro h
    exact hcross (P.part_equiv.trans hxz h)
  have hraw : P.colour x (T z) = P.colour y z := by
    simpa only [hTy] using hTcolour y z
  have hEff :
      P.effectiveReduct.F x (T z) = d.s (a * g) := by
    calc
      P.effectiveReduct.F x (T z) =
          P.effectiveReduct.F y z :=
        P.effectiveReduct_equalColour x (T z) y z hraw hxTz
      _ = d.s (P.effectiveReduct.F z y) := by
        have hr := P.effectiveReduct.reverse_cross z y
        have hzyEff : ¬P.effectiveReduct.part z y := hzyCross
        exact hr hzyEff
      _ = d.s (a * g) := by rw [hzy]
  exact P.goodCongruence_of_swappedRectangle
    T hTcolour x z y (T z)
    hxz hyTz hcross a g hgFixed rfl hzy hEff
    rfl (hTtwo z)

/-- In particular, with no complete good orbit, there can be NO
cross-class transposition by a genuine involutive raw automorphism
of a structure with all the needed relative row realizations. -/
theorem no_crossInvolution_of_noCompleteGoodOrbit_and_rows
    (P : RawRectanglePresentation d V)
    (hNoOrbit : ¬d.HasCompleteGoodOrbit)
    (T : Equiv.Perm V)
    (hTcolour : ∀ x y : V,
      P.colour (T x) (T y) = P.colour x y)
    (hTtwo : ∀ z : V, T (T z) = z)
    (x y : V)
    (hcross : ¬P.part x y)
    (hTx : T x = y)
    (hTy : T y = x)
    (hRows : ∀ a : G,
      ∃ z : V, P.part x z ∧
        P.effectiveReduct.F z y =
          a * P.effectiveReduct.F x y) :
    False := by
  have hGood :=
    P.completeGoodOrbitAt_of_crossInvolution_and_rowRealization
      T hTcolour hTtwo x y hcross hTx hTy hRows
  exact hNoOrbit
    ((d.hasCompleteGoodOrbit_iff_exists_goodCompleteOrbitAt).2
      ⟨P.effectiveReduct.F x y, hGood⟩)

end RawRectanglePresentation
end SemigenericEPPA
