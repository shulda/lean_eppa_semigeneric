import SemigenericEPPA.Bridge.CoherentOrbitSwappedPair
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport

/-!
# Incomplete good affine orbits supply an explicit DLF orbit killer

The negative side of DLF needs a parameter a such that the
congruence transform of a currently good effective colour g has
NO reversal-fixed raw lift. The existence of a parameter is a
direct logical consequence of having no complete good orbit.

For the resulting rectangle obstruction, the already certified
swapped-rectangle lemma calculates the bottom-right effective
colour as exactly congruence(s,a,g). An involution swapping that
cross-part pair would force this colour to be good, contradiction.

This module proves the negative implication CONDITIONAL on the
existence of the prescribed rectangle and involution. The
subsequent extension lemma which creates this rectangle over a
prescribed finite action pair is not asserted here.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {d : RawDatum G C}

/-- When no complete good affine congruence orbit exists, EVERY
good effective seed g admits a concrete parameter a taking it
outside the good set. The affine action is the original one,
including the possible nontrivial s(1) term. -/
theorem RawDatum.exists_badCongruence_parameter
    (d : RawDatum G C)
    (hNoOrbit : ¬d.HasCompleteGoodOrbit)
    (g : G)
    (hg : g ∈ d.selfReverseEffective) :
    ∃ a : G, congruence d.s a g ∉ d.selfReverseEffective := by
  classical
  by_contra hn
  apply hNoOrbit
  refine ⟨g, hg, ?_⟩
  intro a
  by_contra hbad
  exact hn ⟨a, hbad⟩

/-- A concrete bad congruence parameter forbids any raw-colour-
preserving automorphism swapping the two specified endpoints in
the standard orbit-killing rectangle. This assertion uses only
the exact R1--R3 rectangle law; no choice of a global witness
or order-two extension is hidden in the hypotheses. -/
theorem RawRectanglePresentation.noSwappedOrbitKillerRectangle
    (P : RawRectanglePresentation d V)
    (T : Equiv.Perm V)
    (hTcolour : ∀ x y, P.colour (T x) (T y) = P.colour x y)
    (u v z w : V)
    (huv : P.part u v)
    (hzw : P.part z w)
    (huz : ¬P.part u z)
    (a g : G)
    (hgfixed : d.s g = g)
    (hbad : congruence d.s a g ∉ d.selfReverseEffective)
    (huzg : P.effectiveReduct.F u z = g)
    (hvza : P.effectiveReduct.F v z = a * g)
    (huw : P.effectiveReduct.F u w = d.s (a * g))
    (hTv : T v = w)
    (hTw : T w = v) :
    False := by
  exact hbad
    (P.goodCongruence_of_swappedRectangle T hTcolour
      u v z w huv hzw huz a g hgfixed
      huzg hvza huw hTv hTw)

/-- Under the absence of a complete good orbit, a fixed good
seed always gives a parameter whose prescribed rectangle is
incompatible with any swapping raw automorphism. -/
theorem RawRectanglePresentation.noSwappedOrbitKiller_of_noCompleteOrbit
    (P : RawRectanglePresentation d V)
    (hNoOrbit : ¬d.HasCompleteGoodOrbit)
    (g : G)
    (hg : g ∈ d.selfReverseEffective)
    (hgfixed : d.s g = g) :
    ∃ a : G,
      congruence d.s a g ∉ d.selfReverseEffective ∧
      ∀ (T : Equiv.Perm V)
        (hTcolour : ∀ x y, P.colour (T x) (T y) = P.colour x y)
        (u v z w : V),
        P.part u v →
        P.part z w →
        ¬P.part u z →
        P.effectiveReduct.F u z = g →
        P.effectiveReduct.F v z = a * g →
        P.effectiveReduct.F u w = d.s (a * g) →
        T v = w →
        T w = v →
        False := by
  obtain ⟨a, hbad⟩ := d.exists_badCongruence_parameter hNoOrbit g hg
  refine ⟨a, hbad, ?_⟩
  intro T hTcolour u v z w huv hzw huz huzg hvza huw hTv hTw
  exact P.noSwappedOrbitKillerRectangle T hTcolour
    u v z w huv hzw huz a g hgfixed hbad
    huzg hvza huw hTv hTw

end SemigenericEPPA
