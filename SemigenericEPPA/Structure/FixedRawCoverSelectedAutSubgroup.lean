import SemigenericEPPA.Structure.FixedRawCoverSelectedSubgroupAction
import SemigenericEPPA.Bridge.BinaryRawAutomorphismSubgroup

/-!
# Selected old raw H-actions land in the literal raw automorphism group

The fixed joint raw cover comes with a homomorphic action lift on
its zero-section, provided the chosen effective action is truly
flip-safe. The final coherent groupoid construction requires the
lift in the SAME genuine automorphism GROUP of the raw witness,
not merely a family of permutations carrying E and each R_c
invariance proofs as additional external conditions.

The certified elementary BinaryRawAutomorphismSubgroup framework
turns that strict whole-cover permutation homomorphism into a
homomorphism of actual raw relational automorphism groups, while
preserving the literal embedded selected old vertices exactly.

This lemma introduces no new raw cover, code, baseline or action
choice after selecting S/H. Ordinary partial raw connectors and
the simultaneous construction of safe effective H-actions are
independent gates.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {C : Type w} {U : Type z} {V : Type t}
variable {d : RawDatum G C}

/-- On the one previously fixed raw cover, every genuinely
flip-safe effective H-action extending an actual selected raw
H-action lifts to its LITERAL E- and every R_c-automorphism group.

No selected-old raw-colour reference invariance premise is needed:
the preceding fixed-cover theorem derives that from the genuine
old raw automorphism equations. -/
theorem FixedJointRawCover.exists_rawAutSubgroupLift_of_selectedRawAction
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (e : U → V)
    (J : FixedJointRawCover.{v, w, z, t, u} P D e)
    (he : Function.Injective e)
    (hPartEmbed : ∀ x y : U,
      D.part (e x) (e y) ↔ P.part x y)
    (S : Set U)
    (rhoS : H →* Equiv.Perm S)
    (Theta : H →* Equiv.Perm V)
    (hOld : ∀ (h : H) (x : S),
      Theta h (e x.val) = e (rhoS h x).val)
    (hPartOld : ∀ (h : H) (x y : S),
      P.part (rhoS h x).val (rhoS h y).val ↔
        P.part x.val y.val)
    (hColourOld : ∀ (h : H) (x y : S),
      P.colour (rhoS h x).val (rhoS h y).val =
        P.colour x.val y.val)
    (hThetaPart : ∀ (h : H) (x y : V),
      D.part (Theta h x) (Theta h y) ↔ D.part x y)
    (hThetaColour : ∀ (h : H) (x y : V), ¬D.part x y →
      D.F (Theta h x) (Theta h y) = D.F x y)
    (hFlip : ∀ (h : H) (x y : V), ¬D.part x y →
      Theta h x = y → Theta h y = x →
        ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c) :
    ∃ lift : H →* binaryRawAutSubgroup
        (fun X Y : RawCoverVertex V (UniversalResidualCarrier C) =>
          D.part X.1 Y.1)
        (fun c X Y =>
          rawRel (rawCoverPresentation D J.code J.baseline
            J.baseline_reverse).toStructure c X Y),
      ∀ (h : H) (x : S),
        (lift h).val
          (e x.val, fun _ : V => (0 : UniversalResidualCarrier C)) =
          (e (rhoS h x).val,
            fun _ : V => (0 : UniversalResidualCarrier C)) := by
  obtain ⟨perm, hOldLift, hPart, hRel⟩ :=
    FixedJointRawCover.exists_rawGroupLift_of_selectedRawAction
      P D e J he hPartEmbed S rhoS Theta
      hOld hPartOld hColourOld hThetaPart hThetaColour hFlip
  let E : RawCoverVertex V (UniversalResidualCarrier C) →
      RawCoverVertex V (UniversalResidualCarrier C) → Prop :=
    fun X Y => D.part X.1 Y.1
  let R : C → RawCoverVertex V (UniversalResidualCarrier C) →
      RawCoverVertex V (UniversalResidualCarrier C) → Prop :=
    fun c X Y =>
      rawRel (rawCoverPresentation D J.code J.baseline
        J.baseline_reverse).toStructure c X Y
  have hPres : ∀ h : H, PreservesBinaryRawRelations E R (perm h) := by
    intro h
    exact ⟨hPart h, hRel h⟩
  let lift : H →* binaryRawAutSubgroup E R :=
    binaryRawAutHom E R perm hPres
  refine ⟨lift, ?_⟩
  intro h x
  exact hOldLift h x

end SemigenericEPPA
