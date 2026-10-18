import SemigenericEPPA.Bridge.CoherentOrbitSwappedPair

/-!
# Involutive transposition forces the coherent congruence obstruction

In the manuscript's negative coherent-EPPA argument, the partial
transposition u↔z is extended coherently to a total involution T.
With v in the old part of u, its image w=T(v) belongs to the part
of z, and involutivity swaps v and w.

Assuming only that T preserves all raw colours and E, we deduce
the formerly prescribed fourth corner of the rectangle:
  F(u,w)=s(F(v,z)).
Then the certified swapped-pair rectangle lemma forces the
effective colour a⋆g to possess a self-reversing raw preimage.

This theorem needs NO additional guess about the new vertex w or
its incident effective colours. The still missing global step is
to obtain such an involution from a coherent groupoid extension,
and to construct the finite three-vertex obstruction inside each
raw class with g in the good set.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}

/-- A raw automorphism T which is a genuine involution and swaps
the two endpoints u,z of an old self-reversing edge forces the
congruence orbit colour a⋆g to possess a self-reversing raw colour,
provided another vertex v in u's part has F(v,z)=a*g.

The proof derives all facts involving the new point T(v) from
T²=1, colour preservation, E preservation, and the literal
affine reversal on cross-part effective colours. -/
theorem RawRectanglePresentation.goodCongruence_of_involutiveSwap
    (P : RawRectanglePresentation d V)
    (T : Equiv.Perm V)
    (hTcolour : ∀ x y, P.colour (T x) (T y) = P.colour x y)
    (hT2 : ∀ x : V, T (T x) = x)
    (u v z : V)
    (huv : P.part u v)
    (huz : ¬P.part u z)
    (hTu : T u = z)
    (a g : G)
    (hg : d.s g = g)
    (huzg : P.effectiveReduct.F u z = g)
    (hvza : P.effectiveReduct.F v z = a * g) :
    congruence d.s a g ∈ d.selfReverseEffective := by
  let D : EffectiveGeometry d.s V := P.effectiveReduct
  have hTpart (x y : V) :
      P.part (T x) (T y) ↔ P.part x y := by
    calc
      P.part (T x) (T y) ↔
          P.colour (T x) (T y) = none :=
            (P.colour_none_iff (T x) (T y)).symm
      _ ↔ P.colour x y = none := by rw [hTcolour x y]
      _ ↔ P.part x y := P.colour_none_iff x y
  have hTz : T z = u := by
    calc
      T z = T (T u) := congrArg T hTu.symm
      _ = u := hT2 u
  let w : V := T v
  have hzw : P.part z w := by
    have h := (hTpart u v).mpr huv
    simpa only [hTu] using h
  have hvz : ¬P.part v z := by
    intro hvz
    exact huz (P.part_equiv.trans huv hvz)
  have hTcross : ¬P.part (T v) (T z) := by
    intro ht
    exact hvz ((hTpart v z).mp ht)
  have hEff :
      D.F (T v) (T z) = D.F v z :=
    P.effectiveReduct_equalColour
      (T v) (T z) v z (hTcolour v z) hTcross
  have hwu : D.F w u = a * g := by
    change D.F (T v) u = a * g
    rw [← hTz]
    exact hEff.trans hvza
  have huwCross : ¬P.part u w := by
    intro h
    exact huz (P.part_equiv.trans h (P.part_equiv.symm hzw))
  have hwuCross : ¬D.part w u := by
    intro h
    have h' : P.part w u := (P.effectiveReduct_part w u).mp h
    exact huwCross (P.part_equiv.symm h')
  have huw : D.F u w = d.s (a * g) := by
    calc
      D.F u w = d.s (D.F w u) :=
        D.reverse_cross w u hwuCross
      _ = d.s (a * g) :=
        congrArg d.s.toFun hwu
  exact P.goodCongruence_of_swappedRectangle
    T hTcolour u v z w huv hzw huz a g hg
    huzg hvza huw rfl (hT2 v)

end SemigenericEPPA
