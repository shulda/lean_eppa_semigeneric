import SemigenericEPPA.Valuations.PaddedPartialIsomorphism
import SemigenericEPPA.Valuations.PartialGaugeFromGeometry
import SemigenericEPPA.Valuations.PaddedGaugeDiagonal
import SemigenericEPPA.Structure.PaddedQuotientEquiv

/-!
# Unconditional old partial-map data after uniform effective padding

The first half of E0 has several verified constructions:
* uniform effective padding of arbitrary finite old geometry;
* a real-label permutation π extending an arbitrary injective old
  partial E-map and a compatible E-class permutation ι;
* exact translation of the old E/F partial map to a padded subtype;
* the true group-valued cross matrix implies the simultaneous
  noncommutative affine multiplier equations (3.14)--(3.15);
* normalized self-gauges on the padded geometry.

Here we compose them and eliminate all intermediate existential
hypotheses: ANY injective partial automorphism of the original finite
effective structure supplies π, ι and a concrete m on *all* padded
E-classes, satisfying the actual (3.13)--(3.15) equations.

This is still NOT the effective EPPA theorem: the next task is to
define the twists L from these parameters and prove that one
prescribed witness automorphism extends the entire old valuation
vertex, not merely its class and old real-label coordinate.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- A literal finite partial isomorphism of the original effective
rectangle geometry produces *all* old E-class and real-label
permutations and the globally compatible old gauge multipliers on
its actual uniform padding. No same-part dummy-F normalization is
imposed on the original geometry; the padding supplies it.

Both the empty partial domain and nonuniform original class sizes
are covered. The output does not assert the final EPPA automorphism. -/
theorem exists_paddedPartialParameters
    [Finite V]
    (D : EffectiveGeometry s V)
    (S : Set V) (p : S → V)
    (hp : Function.Injective p)
    (hE : ∀ x y : S,
      D.part x.val y.val ↔ D.part (p x) (p y))
    (hF : ∀ x y : S, ¬D.part x.val y.val →
      D.F (p x) (p y) = D.F x.val y.val) :
    ∃ (ι : Equiv.Perm (Quotient D.uniformPaddedGeometry.part))
      (π : Equiv.Perm (Quotient D.part × V))
      (m : Quotient D.uniformPaddedGeometry.part →
        Quotient D.uniformPaddedGeometry.part → G),
      (∀ z : Quotient D.part × V,
        Quotient.mk D.uniformPaddedGeometry.part (π z) =
          ι (Quotient.mk D.uniformPaddedGeometry.part z)) ∧
      (∀ x : S,
        π (D.paddedOldMap x.val) = D.paddedOldMap (p x)) ∧
      (∀ (x : D.paddedPartialDomain S)
         (j : Quotient D.uniformPaddedGeometry.part),
        (∃ y : D.paddedPartialDomain S,
          Quotient.mk D.uniformPaddedGeometry.part y.val = j) →
        m (Quotient.mk D.uniformPaddedGeometry.part x.val) j *
          D.uniformPaddedGeometry.toQuotientGauge.vertexGauge x.val j =
            D.uniformPaddedGeometry.toQuotientGauge.vertexGauge
              (D.paddedPartialMap S p x) (ι j)) ∧
      (∀ (i j : Quotient D.uniformPaddedGeometry.part),
        (∃ x : D.paddedPartialDomain S,
          Quotient.mk D.uniformPaddedGeometry.part x.val = i) →
        (∃ y : D.paddedPartialDomain S,
          Quotient.mk D.uniformPaddedGeometry.part y.val = j) →
        i ≠ j →
          s.normalized (m i j) *
            (D.uniformPaddedGeometry.toQuotientGauge.skeleton
              (ι i) (ι j))⁻¹ * m j i =
            (D.uniformPaddedGeometry.toQuotientGauge.skeleton i j)⁻¹) ∧
      (∀ i : Quotient D.uniformPaddedGeometry.part, m i i = 1) := by
  classical
  let B := D.uniformPaddedGeometry
  let T := D.paddedPartialDomain S
  let pp : T → Quotient D.part × V := D.paddedPartialMap S p
  obtain ⟨ιold, π, hπold, _, hπext⟩ :=
    D.exists_paddedPartAndRealPermutations S p hp hE
  let ι : Equiv.Perm (Quotient B.part) := D.paddedPartPermutation ιold
  have hπB : ∀ z : Quotient D.part × V,
      Quotient.mk B.part (π z) = ι (Quotient.mk B.part z) := by
    intro z
    exact (D.paddedPartPermutation_class ιold π hπold z).symm
  have hpp : ∀ x : T,
      ι (Quotient.mk B.part x.val) =
        Quotient.mk B.part (pp x) := by
    intro x
    have hemb : x.val = D.paddedOldMap x.val.2 :=
      D.paddedPartialDomain_eq_old S x
    have hπx : π x.val = pp x := by
      calc
        π x.val = π (D.paddedOldMap x.val.2) :=
          congrArg π hemb
        _ = D.paddedOldMap (p ⟨x.val.2, x.property.2⟩) :=
          hπext ⟨x.val.2, x.property.2⟩
        _ = pp x := rfl
    calc
      ι (Quotient.mk B.part x.val) =
          Quotient.mk B.part (π x.val) := (hπB x.val).symm
      _ = Quotient.mk B.part (pp x) :=
        congrArg (Quotient.mk B.part) hπx
  have hEB : ∀ x y : T,
      B.part x.val y.val ↔ B.part (pp x) (pp y) :=
    D.paddedPartialMap_part_iff S p hE
  have hFB : ∀ x y : T, ¬B.part x.val y.val →
      B.F (pp x) (pp y) = B.F x.val y.val :=
    D.paddedPartialMap_crossColour S p hE hF
  obtain ⟨m, hinc, hcompat, hdiag⟩ :=
    B.exists_partialGaugeMultipliers_from_partialIsomorphism
      (D.uniformPaddedGeometry_samePart_one) T pp hEB hFB ι hpp
  exact ⟨ι, π, m, hπB, hπext, hinc, hcompat, hdiag⟩

end EffectiveGeometry

end SemigenericEPPA
