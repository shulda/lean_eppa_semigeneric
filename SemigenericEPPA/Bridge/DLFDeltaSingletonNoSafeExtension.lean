import SemigenericEPPA.Structure.DLFArbitrarySingletonRawPart
import SemigenericEPPA.Bridge.DLFDeltaProfileInvolutionCrossing

/-!
# The negative DLF delta-profile is an obstruction in ANY larger witness

For old vertices a,c in one E-class and b,c distinct from a,
add a fresh singleton E-class with raw colours selected to give
the effective profile (delta,1,1) on (a,b,c), delta ≠ 1.
All old E and raw R_c relations are preserved exactly.

Now let this enlarged finite presentation embed as an induced raw
substructure into ANY possibly larger original-language raw
rectangle Q. If a raw-colour-preserving involution of Q sends
the old b to a and fixes c, then the geometric three-point
delta obstruction forces the fresh vertex v to cross its E-class.
Under ¬HasCompleteGoodOrbit such an involution cannot be locally
complete-orbit safe.

In particular the parameter/profile is fixed BEFORE choosing the
large witness or involutive extension. No equivariant embedding
or pre-existing H action on the rest of the old structure is assumed.

This is one negative-DLF extension obstruction, not the complete
parity/cofinality argument; obtaining a fixed third point for
arbitrary old group actions remains a separate size-enlargement step.
-/

namespace SemigenericEPPA

universe u v w z
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {d : RawDatum G C}

/-- A single chosen raw profile makes *every* later locally safe
involutive extension of the indicated old swap impossible, provided
there is no complete good affine congruence orbit.

The quantified target Q may have arbitrary additional vertices,
and the induced embedding is required to preserve and reflect the
entire old E relation and every raw colour literally. -/
theorem RawRectanglePresentation.exists_singletonDelta_noSafeInvolutionExtension
    (P : RawRectanglePresentation d V)
    (hNoOrbit : ¬d.HasCompleteGoodOrbit)
    (a b c : V)
    (hac : P.part a c)
    (hba : b ≠ a) (hca : c ≠ a)
    (delta : G) (hdelta : delta ≠ 1) :
    ∃ f : V → C,
      ∀ (W : Type z) (Q : RawRectanglePresentation d W)
        (e : Option V → W),
        (∀ x y : Option V,
          Q.part (e x) (e y) ↔ (P.adjoinSingletonPart f).part x y) →
        (∀ x y : Option V,
          Q.colour (e x) (e y) = (P.adjoinSingletonPart f).colour x y) →
        ∀ (T : Equiv.Perm W),
          (∀ x y : W, Q.colour (T x) (T y) = Q.colour x y) →
          (∀ x : W, T (T x) = x) →
          T (e (some b)) = e (some a) →
          T (e (some c)) = e (some c) →
          (∀ x y : W, ¬Q.part x y →
            T x = y → T y = x →
              d.GoodCompleteOrbitAt (Q.effectiveReduct.F x y)) →
          False := by
  classical
  obtain ⟨f, hfa, hfb, hfc⟩ :=
    P.exists_singletonDeltaProfile a b c hba hca delta
  refine ⟨f, ?_⟩
  intro W Q e hePart heColour T hTcolour hTtwo hTb hTc hSafe
  have hQac : Q.part (e (some a)) (e (some c)) :=
    (hePart (some a) (some c)).mpr
      ((P.adjoinSingletonPart_oldPart f a c).mpr hac)
  have hQva : ¬Q.part (e none) (e (some a)) := by
    intro h
    exact (P.adjoinSingletonPart_newCross f a)
      ((hePart none (some a)).mp h)
  have hEff (x : V) :
      Q.effectiveReduct.F (e none) (e (some x)) =
        (P.adjoinSingletonPart f).effectiveReduct.F none (some x) := by
    have hcol : Q.colour (e none) (e (some x)) = some (f x) := by
      rw [heColour none (some x)]
      rfl
    calc
      Q.effectiveReduct.F (e none) (e (some x)) =
          d.phi (f x) :=
        (Q.effectiveReduct_crossColour
          (e none) (e (some x)) (f x) hcol).symm
      _ = (P.adjoinSingletonPart f).effectiveReduct.F none (some x) :=
        (P.adjoinSingletonPart_effectiveColour f x).symm
  have hQa : Q.effectiveReduct.F (e none) (e (some a)) = delta :=
    (hEff a).trans hfa
  have hQb : Q.effectiveReduct.F (e none) (e (some b)) = 1 :=
    (hEff b).trans hfb
  have hQc : Q.effectiveReduct.F (e none) (e (some c)) = 1 :=
    (hEff c).trans hfc
  exact Q.noSafeDeltaProfileInvolution
    hNoOrbit T hTcolour hTtwo hSafe
    (e (some a)) (e (some b)) (e (some c)) (e none)
    hQac hQva hTb hTc delta hdelta hQa hQb hQc

end SemigenericEPPA
