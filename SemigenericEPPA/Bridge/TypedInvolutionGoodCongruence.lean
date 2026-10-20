import SemigenericEPPA.Bridge.TypedRawAutomorphismPermutation
import SemigenericEPPA.Bridge.CoherentOrbitSwappedPair

/-!
# A typed whole-witness involution forces a good congruence colour

The manuscript's negative coherent-EPPA orbit obstruction uses
a three-old-vertex configuration u E v, with z in another E-class,
and effective cross-colours F(u,z)=g, F(v,z)=a*g, where s(g)=g.

When a typed whole-witness raw automorphism T swaps u and z and
satisfies T²=1, write w=T(v). Exact preservation of the OLD raw
predicates gives z E w, the reverse edge F(u,w)=s(a*g), and a
self-reversing raw colour on the pair v,w. The rectangle law then
forces its effective colour to be a⋆g.

This theorem works with the ACTUAL upstream typed Automorphism
and a real literal raw rectangle presentation, without assuming
a separately provided raw-permutation or an effective-only lift.
The source of the involution from a coherent partial transposition
is certified independently in CoherentClosedSubsetInvolution.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {W : Type w}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- The precise geometric obstruction from a true typed
involution that swaps the first endpoint u with the other-part
endpoint z. It needs only the 3-vertex effective old data; the
fourth rectangle vertex is the image T(v) in the witness. -/
theorem goodCongruence_of_typedInvolution
    (Q : RawRectanglePresentation d W)
    (T : Structure.Automorphism (rectangleTrivialAction C) Q.toStructure)
    (hTinv : ∀ x : W, T (T x) = x)
    (u v z : W)
    (huv : Q.part u v)
    (huz : ¬Q.part u z)
    (hTuz : T u = z)
    (hTzu : T z = u)
    (a g : G) (hg : d.s g = g)
    (huzg : Q.effectiveReduct.F u z = g)
    (hvza : Q.effectiveReduct.F v z = a * g) :
    congruence d.s a g ∈ d.selfReverseEffective := by
  classical
  let perm : Equiv.Perm W := Q.typedAutomorphismPerm T
  let w : W := T v
  have hpermU : perm u = z := hTuz
  have hpermZ : perm z = u := hTzu
  have hpermV : perm v = w := rfl
  have hpermW : perm w = v := hTinv v
  have hzw : Q.part z w := by
    have h := (Q.typedAutomorphismPerm_part T u v).mpr huv
    rw [hpermU, hpermV] at h
    exact h
  let D : EffectiveGeometry d.s W := Q.effectiveReduct
  have huvD : D.part u v := (Q.effectiveReduct_part u v).mpr huv
  have hzwD : D.part z w := (Q.effectiveReduct_part z w).mpr hzw
  have huzD : ¬D.part u z := by
    intro h
    exact huz ((Q.effectiveReduct_part u z).mp h)
  obtain ⟨huwD, hvzD, _hvwD⟩ :=
    D.cross_square u v z w huvD hzwD huzD
  have hcolour : Q.colour u w = Q.colour z v := by
    calc
      Q.colour u w = Q.colour (perm z) (perm v) := by
        rw [hpermZ, hpermV]
      _ = Q.colour z v := Q.typedAutomorphismPerm_colour T z v
  have hcross : ¬Q.part u w := by
    intro h
    exact huwD ((Q.effectiveReduct_part u w).mpr h)
  have heff : D.F u w = D.F z v :=
    Q.effectiveReduct_equalColour u w z v hcolour hcross
  have huw : D.F u w = d.s (a * g) := by
    calc
      D.F u w = D.F z v := heff
      _ = d.s (D.F v z) := D.reverse_cross v z hvzD
      _ = d.s (a * g) := by rw [hvza]
  exact Q.goodCongruence_of_swappedRectangle
    perm (Q.typedAutomorphismPerm_colour T)
      u v z w huv hzw huz a g hg huzg hvza huw
      hpermV hpermW

end RawRectanglePresentation

end SemigenericEPPA
