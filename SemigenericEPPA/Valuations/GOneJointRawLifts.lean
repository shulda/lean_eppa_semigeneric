import SemigenericEPPA.Valuations.GOneEffectiveAndJointRawCover
import SemigenericEPPA.Structure.OldRawReferencePartialInvariance
import SemigenericEPPA.Structure.OldRawReferenceGroupInvariance

/-!
# One raw G=1 witness: ordinary EPPA and all safe stabilizer group lifts

The fixed factorial effective carrier already admits:
* every old partial E-isomorphism as an individual automorphism;
* every raw-colour-preserving H-action on an induced old subset as
  a genuine homomorphism to SAFE effective automorphisms.

The universal fixed raw-cover construction chooses ONE residual code,
baseline, raw presentation and literal old zero-section copy, all
before the later partial map or induced old subgroup.

Here those two certified APIs are finally composed. No abstract
effective extension or old-colour-reference invariance is assumed:
individual extensions come from the fixed factorial effective EPPA
theorem and actual raw reference invariance from the old P-colours.
Safe H-actions come from the factorial replicated-fibre theorem,
and their actual old raw-colour invariance is transferred by the
old reference group lemma.

The resulting SAME finite raw witness has ordinary EPPA and
homomorphic extensions of the automorphism group of EVERY induced
old S. That is not yet a coherent extension FUNCTOR of the full
partial-isomorphism groupoid; picking and certifying connectors
between isomorphic S,T is the remaining C0 gate.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

/-- The same fixed raw-cover carrier for the original P, independent
of S,H and all partial maps. -/
abbrev GOneJointRawCarrier (P : RawRectanglePresentation d A) :=
  RawCoverVertex (GOneFactorialCarrier P) (UniversalResidualCarrier C)

/-- Given the already selected raw cover K, all individual raw
partial automorphisms of P extend to actual automorphisms of its
literal raw predicates from the old ZERO section. -/
def RawRectanglePresentation.HasAllJointRawPartialLifts
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A))
    (K : FixedJointRawCover P P.gOneFactorialGeometry
        (P.gOneFactorialOldMap j)) : Prop :=
  ∀ (S : Set A) (p : S → A),
    Function.Injective p →
    (∀ x y : S, P.part x.val y.val ↔
      P.part (p x) (p y)) →
    (∀ x y : S, P.colour (p x) (p y) =
      P.colour x.val y.val) →
    ∃ T : Equiv.Perm (GOneJointRawCarrier P),
      (∀ x : S,
        T (P.gOneFactorialOldMap j x.val,
          fun _ : GOneFactorialCarrier P =>
            (0 : UniversalResidualCarrier C)) =
          (P.gOneFactorialOldMap j (p x),
            fun _ : GOneFactorialCarrier P =>
              (0 : UniversalResidualCarrier C))) ∧
      (∀ X Y : GOneJointRawCarrier P,
        P.gOneFactorialGeometry.part (T X).1 (T Y).1 ↔
          P.gOneFactorialGeometry.part X.1 Y.1) ∧
      (∀ (c : C) (X Y : GOneJointRawCarrier P),
        rawRel (rawCoverPresentation P.gOneFactorialGeometry
          K.code K.baseline K.baseline_reverse).toStructure c
          (T X) (T Y) ↔
        rawRel (rawCoverPresentation P.gOneFactorialGeometry
          K.code K.baseline K.baseline_reverse).toStructure c X Y)

/-- Every group action on EVERY induced old raw substructure
extends homomorphically on this SAME fixed raw cover, preserving
all literal old raw colours and old zero-section vertices. -/
def RawRectanglePresentation.HasAllJointRawGroupLifts
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A))
    (K : FixedJointRawCover P P.gOneFactorialGeometry
        (P.gOneFactorialOldMap j)) : Prop :=
  ∀ (H : Type t) [Group H]
      (S : Set A) (rho : H →* Equiv.Perm S),
    (∀ h : H, ∀ x y : S,
      P.part x.val y.val ↔
        P.part (rho h x).val (rho h y).val) →
    (∀ h : H, ∀ x y : S,
      P.colour (rho h x).val (rho h y).val =
        P.colour x.val y.val) →
    ∃ lift : H →* Equiv.Perm (GOneJointRawCarrier P),
      (∀ h : H, ∀ x : S,
        lift h (P.gOneFactorialOldMap j x.val,
          fun _ : GOneFactorialCarrier P =>
            (0 : UniversalResidualCarrier C)) =
          (P.gOneFactorialOldMap j (rho h x).val,
            fun _ : GOneFactorialCarrier P =>
              (0 : UniversalResidualCarrier C))) ∧
      (∀ h : H, ∀ X Y : GOneJointRawCarrier P,
        P.gOneFactorialGeometry.part
          (lift h X).1 (lift h Y).1 ↔
        P.gOneFactorialGeometry.part X.1 Y.1) ∧
      (∀ h : H, ∀ c : C, ∀ X Y : GOneJointRawCarrier P,
        rawRel (rawCoverPresentation P.gOneFactorialGeometry
          K.code K.baseline K.baseline_reverse).toStructure c
          (lift h X) (lift h Y) ↔
        rawRel (rawCoverPresentation P.gOneFactorialGeometry
          K.code K.baseline K.baseline_reverse).toStructure c X Y)

/-- One fixed raw EPPA witness and one fixed zero-section embedding
support ALL ordinary partial extensions AND all induced old
automorphism-group homomorphic lifts with no other assumptions. -/
theorem RawRectanglePresentation.exists_gOneJointRawEPPA_andAllGroupLifts
    (P : RawRectanglePresentation d A) :
    ∃ (j : A → Fin (coherentPaddingSize A))
      (K : FixedJointRawCover P P.gOneFactorialGeometry
        (P.gOneFactorialOldMap j)),
      Function.Injective (P.gOneFactorialOldMap j) ∧
      (∀ x y : A,
        P.gOneFactorialGeometry.part
          (P.gOneFactorialOldMap j x)
          (P.gOneFactorialOldMap j y) ↔ P.part x y) ∧
      P.HasAllJointRawPartialLifts j K ∧
      P.HasAllJointRawGroupLifts j K := by
  classical
  obtain ⟨j, K, he, hpart, hpartial, hsafe⟩ :=
    P.exists_gOneEffectiveAndJointRawCover
  let e : A → GOneFactorialCarrier P := P.gOneFactorialOldMap j
  let D := P.gOneFactorialGeometry
  have hpart' : ∀ x y : A,
      D.part (e x) (e y) ↔ P.part x y := hpart
  refine ⟨j, K, he, hpart, ?_, ?_⟩
  · intro S p hp hE hRaw
    obtain ⟨theta, hExt, hEtheta, hFtheta⟩ :=
      hpartial S p hp hE
    have hOldInv (x y : S)
        (hcross : ¬D.part (e x.val) (e y.val)) :
        oldRawReferenceOnBase P e K.defaultColour
            (e (p x)) (e (p y)) =
          oldRawReferenceOnBase P e K.defaultColour
            (e x.val) (e y.val) :=
      oldRawReferenceOnBase_partialInvariant
        P D e he K.defaultColour hpart' S p hE hRaw
        x y hcross
    exact K.individual S p theta hOldInv hExt hEtheta hFtheta
  · intro H _ S rho hE hRaw
    obtain ⟨theta, hExt, hEtheta, hFtheta, hSafe⟩ :=
      hsafe H S rho hE hRaw
    let W : Set (GOneFactorialCarrier P) :=
      Set.range (fun x : S => e x.val)
    have hSubset : W ⊆ Set.range e := by
      intro v hv
      obtain ⟨x, hx⟩ := hv
      exact ⟨x.val, hx⟩
    have hW (h : H) (x : GOneFactorialCarrier P)
        (hx : x ∈ W) : theta h x ∈ W := by
      obtain ⟨a, ha⟩ := hx
      refine ⟨rho h a, ?_⟩
      rw [← ha, hExt h a]
    have hOldInv (h : H) (x y : GOneFactorialCarrier P)
        (hx : x ∈ W) (hy : y ∈ W)
        (hcross : ¬D.part x y) :
        oldRawReferenceOnBase P e K.defaultColour
          (theta h x) (theta h y) =
        oldRawReferenceOnBase P e K.defaultColour x y :=
      oldRawReferenceOnBase_groupInvariant
        P D e he K.defaultColour hpart'
          S rho hE hRaw theta hExt
          h x y hx hy hcross
    have hSafety (h : H) (x y : GOneFactorialCarrier P)
        (hcross : ¬D.part x y)
        (_hOutside : ¬(x ∈ W ∧ y ∈ W))
        (hxy : theta h x = y)
        (hyx : theta h y = x) :
        ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c :=
      hSafe h x y hcross hxy hyx
    obtain ⟨lift, hZero, hPart, hRawPres⟩ :=
      K.safe_groups H theta W hSubset hEtheta hFtheta
        hW hOldInv hSafety
    refine ⟨lift, ?_, hPart, hRawPres⟩
    intro h x
    have hx : e x.val ∈ W := ⟨x, rfl⟩
    have hz := hZero h (e x.val) hx
    rw [hExt h x] at hz
    exact hz

end SemigenericEPPA
