import SemigenericEPPA.Algebra.PartialGaugeFamilies
import SemigenericEPPA.Structure.QuotientGaugeConverse

/-!
# Instantiate partial gauge multipliers from an actual effective partial map

This is the formerly missing geometric input to manuscript
equations (3.14)--(3.15).  For a genuine partial isomorphism of the
effective group-coloured E-rectangle geometry, the canonical
quotient-gauge expressions of every cross-part colour are equal
on the domain and image.  The simultaneous anchored-multiplier
theorem now produces one m(i,j) on all old E-class indices.

We do NOT assume the gauge-matrix preservation equations as a
hypothesis: they are derived here from preservation of the actual
effective colour F, its rectangle-gauge reconstruction, and exact
preservation/reflection of E. We do assume normality of irrelevant
same-part dummy F-values (F(x,y)=1 when xEy). The explicit uniform
padding used in E0 has already been checked to satisfy precisely
this hypothesis, so no extra restriction on the original input is
introduced in the eventual EPPA application.

This lemma constructs all multipliers *simultaneously*, with
(3.14), (3.15), and diagonal m(i,i)=1, for arbitrary affine
anti-involutions and noncommutative groups. The subsequent witness
automorphism/valuation-coordinate assembly is still a separate
step; neither ordinary EPPA nor coherent EPPA is asserted here.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

variable (D : EffectiveGeometry s V)

/-- A colour-preserving old partial E-isomorphism determines
one compatible gauge multiplier family m on *all* quotient
E-class pairs. The partial domain may be empty.

When a target class j is met by the domain, all source vertices x
satisfy the literal equation (3.14). On any two distinct met
classes i,j, the same m satisfies the full affine (3.15).
The diagonal multipliers are literally neutral. -/
theorem exists_partialGaugeMultipliers_from_partialIsomorphism
    (hSame : ∀ x y : V, D.part x y → D.F x y = 1)
    (S : Set V) (p : S → V)
    (hE : ∀ x y : S,
      D.part x.val y.val ↔ D.part (p x) (p y))
    (hF : ∀ x y : S, ¬D.part x.val y.val →
      D.F (p x) (p y) = D.F x.val y.val)
    (ι : Equiv.Perm (Quotient D.part))
    (hι : ∀ x : S,
      ι (Quotient.mk D.part x.val) = Quotient.mk D.part (p x)) :
    ∃ m : Quotient D.part → Quotient D.part → G,
      (∀ (x : S) (j : Quotient D.part),
        (∃ y : S, Quotient.mk D.part y.val = j) →
        m (Quotient.mk D.part x.val) j *
          D.toQuotientGauge.vertexGauge x.val j =
            D.toQuotientGauge.vertexGauge (p x) (ι j)) ∧
      (∀ (i j : Quotient D.part),
        (∃ x : S, Quotient.mk D.part x.val = i) →
        (∃ y : S, Quotient.mk D.part y.val = j) →
        i ≠ j →
          s.normalized (m i j) *
            (D.toQuotientGauge.skeleton (ι i) (ι j))⁻¹ *
              m j i =
            (D.toQuotientGauge.skeleton i j)⁻¹) ∧
      (∀ i : Quotient D.part, m i i = 1) := by
  classical
  let cls : V → Quotient D.part := Quotient.mk D.part
  let a : V → Quotient D.part → G := D.toQuotientGauge.vertexGauge
  let K : Quotient D.part → Quotient D.part → G :=
    D.toQuotientGauge.skeleton
  have hdiag (x : V) : a x (cls x) = 1 := by
    change D.F (D.representative (Quotient.mk D.part x)) x = 1
    exact hSame _ _ (D.part.iseqv.symm (D.related_representative x))
  have hpart (x : S) : cls (p x) = ι (cls x.val) :=
    (hι x).symm
  have hcolour (x y : S) (hxy : cls x.val ≠ cls y.val) :
      gaugeColour s (a x.val (cls y.val))
          (K (cls x.val) (cls y.val)) (a y.val (cls x.val)) =
        gaugeColour s (a (p x) (ι (cls y.val)))
          (K (ι (cls x.val)) (ι (cls y.val)))
          (a (p y) (ι (cls x.val))) := by
    have hcross : ¬D.part x.val y.val := by
      intro h
      exact hxy (Quotient.sound h)
    have hcross' : ¬D.part (p x) (p y) := by
      intro h
      exact hcross ((hE x y).mpr h)
    have hfirst := D.toQuotientGauge.effective_cross x.val y.val hcross
    have hreconstruct :=
      D.quotientGauge_reconstruct_cross x.val y.val hcross
    have hsecond :=
      D.toQuotientGauge.effective_cross (p x) (p y) hcross'
    have hreconstruct' :=
      D.quotientGauge_reconstruct_cross (p x) (p y) hcross'
    calc
      gaugeColour s (a x.val (cls y.val))
          (K (cls x.val) (cls y.val)) (a y.val (cls x.val)) =
        D.F x.val y.val := hfirst.symm.trans hreconstruct
      _ = D.F (p x) (p y) := (hF x y hcross).symm
      _ = gaugeColour s (a (p x) (ι (cls y.val)))
          (K (ι (cls x.val)) (ι (cls y.val)))
          (a (p y) (ι (cls x.val))) := by
        calc
          D.F (p x) (p y) =
            D.toQuotientGauge.toEffectiveGeometry.F (p x) (p y) :=
              hreconstruct'.symm
          _ = gaugeColour s (a (p x) (ι (cls y.val)))
                (K (ι (cls x.val)) (ι (cls y.val)))
                (a (p y) (ι (cls x.val))) := by
              simpa only [hι x, hι y] using hsecond
  let m : Quotient D.part → Quotient D.part → G :=
    partialGaugeMultiplier S p ι cls a
  obtain ⟨hinc, hcompat⟩ :=
    partialGaugeMultiplier_properties s S p ι cls a K
      hdiag hpart hcolour
  refine ⟨m, ?_, ?_, ?_⟩
  · exact hinc
  · exact hcompat
  · intro i
    exact partialGaugeMultiplier_diag S p ι cls a i

end EffectiveGeometry

end SemigenericEPPA
