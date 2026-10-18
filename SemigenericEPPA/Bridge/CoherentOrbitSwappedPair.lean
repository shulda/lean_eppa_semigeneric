import SemigenericEPPA.Bridge.CoherentOrbitRectangle
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge

/-!
# Raw reversal and the coherent congruence obstruction

An automorphism that interchanges two vertices from different
E-classes forces their raw edge colour to be self-reversing.
Combining that observation with the exact affine rectangle identity
shows that the fourth effective edge colour in the obstruction
rectangle belongs to the set of self-reversing effective colours.

This is precisely the *local* mathematical forcing implication
used in the necessity proof of Section 4 of the manuscript. A
future groupoid/coherence step must guarantee existence of the
appropriate involutive witness automorphism from the partial
transposition; no coherent-EPPA classification is assumed here.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}

/-- A raw-colour preserving permutation which swaps an old
cross-E pair forces its literal raw colour to be fixed by the
raw reversal, not just its effective group colour. -/
theorem RawRectanglePresentation.selfReverse_of_swappedPair
    (P : RawRectanglePresentation d V)
    (T : Equiv.Perm V)
    (hTcolour : ∀ x y, P.colour (T x) (T y) = P.colour x y)
    (v w : V) (hvw : ¬P.part v w)
    (hTv : T v = w) (hTw : T w = v) :
    ∃ c : C, P.colour v w = some c ∧ d.reverse c = c := by
  have hswap : P.colour w v = P.colour v w := by
    calc
      P.colour w v = P.colour (T v) (T w) := by
        rw [hTv, hTw]
      _ = P.colour v w := hTcolour v w
  cases hc : P.colour v w with
  | none =>
      exact False.elim (hvw ((P.colour_none_iff v w).mp hc))
  | some c =>
      have hrev : P.colour w v = some (d.reverse c) := by
        rw [P.colour_reverse v w, hc]
        rfl
      have hfix : d.reverse c = c := by
        apply Option.some.inj
        exact hrev.symm.trans (hswap.trans hc)
      exact ⟨c, rfl, hfix⟩

/-- The full *local* congruence-orbit forcing implication for the
standard coherent EPPA obstruction rectangle.

The first edge has s-fixed colour g, the second row's first edge
is a*g, and the top-right edge is the raw-reversed effective colour
s(a*g). If a raw automorphism swaps the two lower/right endpoints
v,w, the fourth edge is self-reversing, so a⋆g is a good effective
colour. No assumptions on global EPPA witnesses or groupoids are
made. -/
theorem RawRectanglePresentation.goodCongruence_of_swappedRectangle
    (P : RawRectanglePresentation d V)
    (T : Equiv.Perm V)
    (hTcolour : ∀ x y, P.colour (T x) (T y) = P.colour x y)
    (u v z w : V)
    (huv : P.part u v)
    (hzw : P.part z w)
    (huz : ¬P.part u z)
    (a g : G) (hg : d.s g = g)
    (huzg : P.effectiveReduct.F u z = g)
    (hvza : P.effectiveReduct.F v z = a * g)
    (huw : P.effectiveReduct.F u w = d.s (a * g))
    (hTv : T v = w) (hTw : T w = v) :
    congruence d.s a g ∈ d.selfReverseEffective := by
  let D : EffectiveGeometry d.s V := P.effectiveReduct
  have huvD : D.part u v := (P.effectiveReduct_part u v).mpr huv
  have hzwD : D.part z w := (P.effectiveReduct_part z w).mpr hzw
  have huzD : ¬D.part u z := by
    intro h
    exact huz ((P.effectiveReduct_part u z).mp h)
  obtain ⟨_, _, hvwD⟩ :=
    D.cross_square u v z w huvD hzwD huzD
  have hvw : ¬P.part v w := by
    intro h
    exact hvwD ((P.effectiveReduct_part v w).mpr h)
  have hquad :
      D.F v w = congruence d.s a g :=
    D.congruence_colour_of_rectangle u v z w huvD hzwD
      huzD a g hg huzg hvza huw
  obtain ⟨c, hc, hfix⟩ :=
    P.selfReverse_of_swappedPair T hTcolour v w hvw hTv hTw
  have heff : d.phi c = D.F v w :=
    P.effectiveReduct_crossColour v w c hc
  exact ⟨c, heff.trans hquad, hfix⟩

end SemigenericEPPA
