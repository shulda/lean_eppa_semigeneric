import SemigenericEPPA.Structure.DLFFiniteSafePairEmbeddings
import SemigenericEPPA.Structure.DLFFullRawAutomorphismGroup

/-!
# Every original raw subgroup action is locally safe when G=1

The positive dense locally finite classification has an exceptional
case with trivial effective group G, even when the original raw
palette has NO reversal-fixed colour.

The finite safe-pair invariant does not obstruct this branch:
if an original raw automorphism reverses an E-cross ordered pair
(x,y), it fixes the LITERAL raw colour of that pair under reversal.
Hence the effective group colour is good. When G is subsingleton,
its ENTIRE affine congruence orbit is that one colour.

This proof works for ANY raw automorphism subgroup, not only
square-one elements and without assuming HasCompleteGoodOrbit.
It is a useful bridge from certified G=1 coherent EPPA subgroup
lifts to the actual finite-safe-pair tower machinery.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Subsingleton G]
variable {C : Type v}
variable {V : Type w} [Finite V]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- For trivial effective G, an arbitrary literal raw automorphism
interchanging endpoints of a cross-part edge has a COMPLETE good
congruence orbit there. No existence of a fixed raw colour is
assumed globally; it is forced locally by that automorphism. -/
theorem gOne_swappedCrossPair_goodCompleteOrbit
    (P : RawRectanglePresentation d V)
    (g : P.fullRawAutGroup)
    (x y : V) (hcross : ¬P.part x y)
    (hxy : g.val x = y) (hyx : g.val y = x) :
    d.GoodCompleteOrbitAt (P.effectiveReduct.F x y) := by
  have hSwapColour : P.colour y x = P.colour x y := by
    have h := P.fullRawAutGroup_colour g x y
    rw [hxy, hyx] at h
    exact h
  have hGood : P.effectiveReduct.F x y ∈ d.selfReverseEffective := by
    cases hc : P.colour x y with
    | none =>
        exact False.elim (hcross ((P.colour_none_iff x y).mp hc))
    | some c =>
        have hFix : d.reverse c = c := by
          have h := P.colour_reverse x y
          rw [hSwapColour, hc] at h
          change some c = some (d.reverse c) at h
          exact (Option.some.inj h).symm
        rw [← P.effectiveReduct_crossColour x y c hc]
        exact ⟨c, rfl, hFix⟩
  intro a
  have heq :
      congruence d.s a (P.effectiveReduct.F x y) =
        P.effectiveReduct.F x y := Subsingleton.elim _ _
  rw [heq]
  exact hGood

/-- Every finite original E/R_c presentation with trivial effective
group and ANY chosen genuine subgroup K≤Aut_raw(P) is a locally
safe finite pair, with no global good-orbit assumption. -/
noncomputable def gOne_safePair
    (P : RawRectanglePresentation d V)
    (K : Subgroup P.fullRawAutGroup) :
    FiniteSafeRawPair d V where
  raw := P
  subgroup := K
  safe := by
    intro h _ x y hcross hxy hyx
    exact P.gOne_swappedCrossPair_goodCompleteOrbit
      h.val x y hcross hxy hyx

end RawRectanglePresentation
end SemigenericEPPA
