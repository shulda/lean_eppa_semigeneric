import SemigenericEPPA.Bridge.SelectedFlipSafeEffectiveHAction
import SemigenericEPPA.Structure.FixedRawCoverSelectedAutSubgroup

/-!
# From genuine selected indexed actions to raw automorphism subgroups

This is the same-data bridge between the indexed selected-substructure
flip-safety theorem and the ONE previously fixed raw cover. The
multiplier matrix and selected reference twists are constructed by
the former theorem; the entire group acts on the latter witness.

There is NO separately assumed effective action Theta, no independent
raw flip-safety premise, and no new code or baseline chosen after H.
Only geometric occupied-projection information and actual raw old
automorphism information remain as inputs.

The selected old zero-section on the fixed raw cover is preserved
literally. The theorem returns a homomorphism into the actual group
of E- and all R_c-preserving permutations, not just abstract
permutations with optional correctness predicates.

The factorial replica construction will discharge the occupied
projection hypotheses in the next integration layer.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w} {U : Type z}
variable {H : Type t} [Group H]
variable {d : RawDatum G C}

/-- Construct the actual strict selected raw automorphism-group lift
on a fixed common raw cover, without postulating an action on the
effective valuation witness or a raw flip-safety conclusion.

The raw old embedding e is identified with the same indexed-gauge
zero-section as the effective action, so the exact selected action
extends to the literal original-language raw zero-section. -/
theorem IndexedGauge.exists_selectedIndexedRawAutSubgroupLift
    (D : EffectiveGeometry d.s V)
    (P : IndexedGauge d.s V (Quotient D.part))
    (hPLabel : ∀ x : V, P.label x = Quotient.mk D.part x)
    (hPColour : ∀ x y : V, ¬D.part x y →
      P.effective x y = D.F x y)
    (hGood : d.selfReverseEffective.Nonempty)
    (hConst : ∀ i j : Quotient D.part,
      P.skeleton i j = Classical.choose hGood)
    (hDiagP : ∀ x : V, P.vertexGauge x (P.label x) = 1)
    (K : EffectiveWitnessSkeleton D)
    (hK : ∀ q r : EffectiveWitnessPart D,
      K.colour q r = Classical.choose hGood)
    (S : Set V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (hF : ∀ (h : H) (x y : S),
      P.label x.val ≠ P.label y.val →
      P.toEffectiveGeometry.F (rho h x.val) (rho h y.val) =
        P.toEffectiveGeometry.F x.val y.val)
    (T : Set U)
    (DS : EffectiveGeometry d.s T)
    (oldRaw : T → T → C)
    (hRawPhi : ∀ a b : T, ¬DS.part a b →
      d.phi (oldRaw a b) = DS.F a b)
    (hRawReverse : ∀ a b : T, ¬DS.part a b →
      oldRaw b a = d.reverse (oldRaw a b))
    (rhoS : H →* Equiv.Perm T)
    (hRawInvariant : ∀ (h : H) (a b : T), ¬DS.part a b →
      oldRaw (rhoS h a) (rhoS h b) = oldRaw a b)
    (occupied : Quotient D.part → Prop)
    (hFixed : ∀ (h : H) (i : Quotient D.part),
      ¬occupied i → iota h i = i)
    (proj : V → Option T)
    (cls : T → Quotient D.part)
    (hSPart : ∀ a b : T,
      DS.part a b ↔ cls a = cls b)
    (hSome : ∀ (w : V),
      occupied (Quotient.mk D.part w) →
        ∃ a : T, proj w = some a)
    (hProj : ∀ (h : H) (w : V),
      proj (rho h w) = Option.map (rhoS h) (proj w))
    (hProjClass : ∀ (w : V) (a : T),
      proj w = some a → Quotient.mk D.part w = cls a)
    (embed : T → V)
    (hEmbedClass : ∀ a : T,
      Quotient.mk D.part (embed a) = cls a)
    (hEmbedAction : ∀ (h : H) (a : T),
      rho h (embed a) = embed (rhoS h a))
    (hEmbedColour : ∀ a b : T, ¬DS.part a b →
      D.F (embed a) (embed b) = DS.F a b)
    (hEmbedMem : ∀ a : T, embed a ∈ S)
    (hsat : d.IsCongruenceSaturated)
    (Praw : RawRectanglePresentation d U)
    (e : U → EffectiveWitnessVertex D)
    (J : FixedJointRawCover Praw K.toEffectiveGeometry e)
    (he : Function.Injective e)
    (hPartEmbed : ∀ a b : U,
      K.toEffectiveGeometry.part (e a) (e b) ↔ Praw.part a b)
    (hOldSection : ∀ a : T,
      e a.val = D.gaugeOldWitnessVertex P.vertexGauge (embed a))
    (hPartOld : ∀ (h : H) (a b : T),
      Praw.part (rhoS h a).val (rhoS h b).val ↔
        Praw.part a.val b.val)
    (hColourOld : ∀ (h : H) (a b : T),
      Praw.colour (rhoS h a).val (rhoS h b).val =
        Praw.colour a.val b.val) :
    ∃ lift : H →* binaryRawAutSubgroup
        (fun X Y : RawCoverVertex
            (EffectiveWitnessVertex D) (UniversalResidualCarrier C) =>
          K.toEffectiveGeometry.part X.1 Y.1)
        (fun c X Y =>
          rawRel (rawCoverPresentation K.toEffectiveGeometry
            J.code J.baseline J.baseline_reverse).toStructure
            c X Y),
      ∀ (h : H) (a : T),
        (lift h).val
          (e a.val, fun _ : EffectiveWitnessVertex D =>
            (0 : UniversalResidualCarrier C)) =
          (e (rhoS h a).val,
            fun _ : EffectiveWitnessVertex D =>
              (0 : UniversalResidualCarrier C)) := by
  obtain ⟨Theta, hOld, hThetaPart, hThetaColour, hFlip⟩ :=
    P.exists_selectedFlipSafeEffectiveHAction
      D hPLabel hPColour hGood hConst hDiagP K hK
      S rho iota hS hcls hF DS oldRaw
      hRawPhi hRawReverse rhoS hRawInvariant occupied
      hFixed proj cls hSPart hSome hProj hProjClass
      embed hEmbedClass hEmbedAction hEmbedColour hEmbedMem hsat
  have hOldActual (h : H) (a : T) :
      Theta h (e a.val) = e (rhoS h a).val := by
    calc
      Theta h (e a.val) =
          Theta h (D.gaugeOldWitnessVertex P.vertexGauge (embed a)) := by
            rw [hOldSection a]
      _ = D.gaugeOldWitnessVertex P.vertexGauge (rho h (embed a)) :=
        hOld h (embed a) (hEmbedMem a)
      _ = D.gaugeOldWitnessVertex P.vertexGauge (embed (rhoS h a)) := by
        rw [hEmbedAction h a]
      _ = e (rhoS h a).val := (hOldSection (rhoS h a)).symm
  exact FixedJointRawCover.exists_rawAutSubgroupLift_of_selectedRawAction
    Praw K.toEffectiveGeometry e J he hPartEmbed
    T rhoS Theta hOldActual hPartOld hColourOld
    hThetaPart hThetaColour hFlip

end SemigenericEPPA
