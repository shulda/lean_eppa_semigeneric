import SemigenericEPPA.Structure.DLFArbitrarySingletonRawPart
import SemigenericEPPA.Bridge.DLFDeltaProfileMovingThirdPoint

/-!
# Universal negative DLF delta obstruction with NO fixed third point

The obstruction for an old involution moving an E-class is valid even
if the involution has NO fixed vertex in that class. The key is a
fresh singleton E-class with an effective row equal to delta≠1 at a
and equal to 1 at EVERY old vertex other than a.

Fix b≠a and c≠a,b in an old E-class with b E c. Suppose a large
raw rectangle witness Q contains this chosen singleton extension
as an induced substructure. Any raw-colour-preserving involution T
of Q extending an old permutation t with t(b)=a must satisfy
F(new,T(c))=1, since t(c)≠a by injectivity of t.
The two columns a,T(c) then give a forbidden [[delta,1],[1,1]]
rank-one rectangle if new E T(new).

Thus under no complete good congruence orbit NO such involution
can be locally safe, regardless of the rest of Q. The profile
is chosen before Q and T; the order of quantifiers is essential.

No requirement T(c)=c, nor any false assumption H acts on the
larger prescribed original structure. The remaining negative DLF
proof must separately create an old three-point part with a
suitable nontrivial involution, then perform the cofinality/parity
argument.
-/

namespace SemigenericEPPA

universe u v w z
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {d : RawDatum G C}

namespace RawRectanglePresentation

/-- A new singleton E-class can realize delta at one distinguished
old vertex a and the identity effective colour at ALL other
old vertices simultaneously, with arbitrary original raw palette
and without an order on V. -/
theorem exists_singletonDeltaProfile_allOther
    (P : RawRectanglePresentation d V)
    (a : V) (delta : G) :
    ∃ f : V → C,
      (P.adjoinSingletonPart f).effectiveReduct.F none (some a) = delta ∧
      (∀ x : V, x ≠ a →
        (P.adjoinSingletonPart f).effectiveReduct.F none (some x) = 1) := by
  classical
  obtain ⟨cdelta, hdelta⟩ := d.phi_surjective delta
  obtain ⟨cone, hone⟩ := d.phi_surjective 1
  let f : V → C := fun x => if x = a then cdelta else cone
  refine ⟨f, ?_, ?_⟩
  · rw [P.adjoinSingletonPart_effectiveColour]
    simp [f, hdelta]
  · intro x hxa
    rw [P.adjoinSingletonPart_effectiveColour]
    simp [f, hxa, hone]

/-- Choose the singleton extension BEFORE any enlarged witness Q,
its embedding, or the involution. For EVERY future Q carrying the
chosen induced copy, no locally safe involution extending the
old permutation t with t(b)=a can exist, even when t has no fixed
point in the old class containing b and c.

The old action t must be defined on the entire original V only
to ensure T(c) remains an old vertex and its row value is 1.
No action on the rest of the enlarged witness is assumed. -/
theorem exists_singletonDelta_noSafeInvolutionExtension_movingThird
    (P : RawRectanglePresentation d V)
    (hNoOrbit : ¬d.HasCompleteGoodOrbit)
    (a b c : V)
    (hba : b ≠ a)
    (hca : c ≠ a)
    (hcb : c ≠ b)
    (hbc : P.part b c)
    (delta : G) (hdelta : delta ≠ 1) :
    ∃ f : V → C,
      ∀ (W : Type z) (Q : RawRectanglePresentation d W)
        (e : Option V → W),
        (∀ x y : Option V,
          Q.part (e x) (e y) ↔ (P.adjoinSingletonPart f).part x y) →
        (∀ x y : Option V,
          Q.colour (e x) (e y) = (P.adjoinSingletonPart f).colour x y) →
        ∀ (t : Equiv.Perm V) (T : Equiv.Perm W),
          (∀ x : V, T (e (some x)) = e (some (t x))) →
          t b = a →
          (∀ x y : W, Q.colour (T x) (T y) = Q.colour x y) →
          (∀ x : W, T (T x) = x) →
          (∀ x y : W, ¬Q.part x y →
            T x = y → T y = x →
              d.GoodCompleteOrbitAt (Q.effectiveReduct.F x y)) →
          False := by
  classical
  obtain ⟨f, hfa, hOther⟩ :=
    P.exists_singletonDeltaProfile_allOther a delta
  refine ⟨f, ?_⟩
  intro W Q e hePart heColour t T hOld htb hTcolour hTtwo hSafe
  have htca : t c ≠ a := by
    intro hc
    have hEq : t c = t b := hc.trans htb.symm
    exact hcb (t.injective hEq)
  have hQbc : Q.part (e (some b)) (e (some c)) :=
    (hePart (some b) (some c)).mpr
      ((P.adjoinSingletonPart_oldPart f b c).mpr hbc)
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
    (hEff b).trans (hOther b hba)
  have hQc : Q.effectiveReduct.F (e none) (e (some c)) = 1 :=
    (hEff c).trans (hOther c hca)
  have hQTc : Q.effectiveReduct.F
      (e none) (T (e (some c))) = 1 := by
    rw [hOld c]
    exact (hEff (t c)).trans (hOther (t c) htca)
  have hTb : T (e (some b)) = e (some a) := by
    rw [hOld b, htb]
  exact Q.noSafeDeltaProfileInvolution_movingThird
    hNoOrbit T hTcolour hTtwo hSafe
    (e (some a)) (e (some b)) (e (some c)) (e none)
    hQbc hQva hTb delta hdelta hQa hQb hQc hQTc

end RawRectanglePresentation
end SemigenericEPPA
