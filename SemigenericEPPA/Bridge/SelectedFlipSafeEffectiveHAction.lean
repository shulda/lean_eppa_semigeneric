import SemigenericEPPA.Valuations.SelectedExplicitRelativeEffectiveHAction
import SemigenericEPPA.Bridge.ReferenceIndexedAllRawFlipsSafeVisited

/-!
# An ACTUAL selected H-action is fully raw flip-safe on one fixed skeleton

A chosen H-action on a selected substructure of an old padded
E-rectangle gives canonical strict multipliers M_h(i,j), reference
twists z and a genuine full two-layer witness action Theta.
The already certified visited-target multiplier theorem proves
both the explicit neutral diagonal M_h(i,i)=1 and the only old
row equations that are genuinely valid (on visited target indices).

Separately, the occupied-only factorial projection onto selected
old RAW vertices ensures every actual swapped cross-pair with
different old indices has a real swapped old pair as its source.
The exact common-middle law and global congruence saturation prove
that its new effective colour admits a reversal-fixed raw lift.
The equal-old-index branch uses M_h(i,i)=1.

This theorem performs the critical SAME-DATA composition:
* use the SAME canonical M in every witness permutation, row
  transport and flip-safety equation;
* use the SAME selected reference z in the actual full H-action;
* use the SAME globally prechosen constant-good witness skeleton K;
* require old raw colour preservation only on the genuinely
  selected old raw structure, not on all padded labels.

The supplied occupied-only projection and its coding remain a
geometric hypothesis here. The factorial replicated-fibre theorem
constructs such projections simultaneously with the auxiliary
old-label H-action in the final construction.

The result is a strict group H→Aut of the effective witness, with
literal old zero-section extension AND complete raw flip-safety.
It does not yet lift to the raw cover or assemble the coherent
partial-isomorphism groupoid.
-/

namespace SemigenericEPPA

universe u v w t z
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w}
variable {H : Type t} [Group H]
variable {S0 : Type z}
variable {d : RawDatum G C}

/-- The actual selected-reference H-action produced from genuine
restricted E/F automorphisms is flip-safe under the exact occupied
projection conditions. Neither the action nor its multiplier matrix
is postulated, and the good witness skeleton K is chosen BEFORE H.

This is the direct effective group-action input to the certified
fixed raw-cover subgroup lift. -/
theorem IndexedGauge.exists_selectedFlipSafeEffectiveHAction
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
    (DS : EffectiveGeometry d.s S0)
    (oldRaw : S0 → S0 → C)
    (hRawPhi : ∀ a b : S0, ¬DS.part a b →
      d.phi (oldRaw a b) = DS.F a b)
    (hRawReverse : ∀ a b : S0, ¬DS.part a b →
      oldRaw b a = d.reverse (oldRaw a b))
    (rhoS : H →* Equiv.Perm S0)
    (hRawInvariant : ∀ (h : H) (a b : S0), ¬DS.part a b →
      oldRaw (rhoS h a) (rhoS h b) = oldRaw a b)
    (occupied : Quotient D.part → Prop)
    (hFixed : ∀ (h : H) (i : Quotient D.part),
      ¬occupied i → iota h i = i)
    (proj : V → Option S0)
    (cls : S0 → Quotient D.part)
    (hSPart : ∀ a b : S0,
      DS.part a b ↔ cls a = cls b)
    (hSome : ∀ (w : V),
      occupied (Quotient.mk D.part w) →
        ∃ a : S0, proj w = some a)
    (hProj : ∀ (h : H) (w : V),
      proj (rho h w) = Option.map (rhoS h) (proj w))
    (hProjClass : ∀ (w : V) (a : S0),
      proj w = some a → Quotient.mk D.part w = cls a)
    (embed : S0 → V)
    (hEmbedClass : ∀ a : S0,
      Quotient.mk D.part (embed a) = cls a)
    (hEmbedAction : ∀ (h : H) (a : S0),
      rho h (embed a) = embed (rhoS h a))
    (hEmbedColour : ∀ a b : S0, ¬DS.part a b →
      D.F (embed a) (embed b) = DS.F a b)
    (hEmbedMem : ∀ a : S0, embed a ∈ S)
    (hsat : d.IsCongruenceSaturated) :
    ∃ Theta : H →* Equiv.Perm (EffectiveWitnessVertex D),
      (∀ (h : H) (x : V), x ∈ S →
        Theta h (D.gaugeOldWitnessVertex P.vertexGauge x) =
          D.gaugeOldWitnessVertex P.vertexGauge (rho h x)) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        K.toEffectiveGeometry.part (Theta h X) (Theta h Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        ¬K.toEffectiveGeometry.part X Y →
          K.toEffectiveGeometry.F (Theta h X) (Theta h Y) =
            K.toEffectiveGeometry.F X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        ¬K.toEffectiveGeometry.part X Y →
          Theta h X = Y → Theta h Y = X →
          ∃ c : C,
            d.phi c = K.toEffectiveGeometry.F X Y ∧
            d.reverse c = c) := by
  obtain ⟨M, hOne, hMul, hDiagM, hVisited, hOld, hE, hFEff⟩ :=
    P.exists_selectedExplicitRelativeEffectiveHAction
      D hPLabel hGood hConst hDiagP K hK
      S rho iota hS hcls hF
  let clsV : V → Quotient D.part :=
    fun w => Quotient.mk D.part w
  let refGauge : V → Quotient D.part → G :=
    selectedReferenceGauge S clsV P.vertexGauge
  let Theta : H →* Equiv.Perm (EffectiveWitnessVertex D) :=
    D.referenceIndexedWitnessAction rho iota refGauge hcls
      M hOne hMul
  have hVisitedSelected : ∀ (h : H) (a : S0)
      (j : Quotient D.part),
      (∃ b : S0, cls b = j) →
      P.vertexGauge (rho h (embed a)) (iota h j) =
        M h (Quotient.mk D.part (embed a)) j *
          P.vertexGauge (embed a) j := by
    intro h a j hj
    obtain ⟨b, hb⟩ := hj
    have hVisitedTarget : ∃ y : V,
        y ∈ S ∧ clsV y = j := by
      refine ⟨embed b, hEmbedMem b, ?_⟩
      exact (hEmbedClass b).trans hb
    exact hVisited h (embed a) (hEmbedMem a) j hVisitedTarget
  have hAllSafe : ∀ (h : H) (X Y : EffectiveWitnessVertex D),
      ¬K.toEffectiveGeometry.part X Y →
      Theta h X = Y → Theta h Y = X →
      ∃ c : C,
        d.phi c = K.toEffectiveGeometry.F X Y ∧
        d.reverse c = c := by
    intro h X Y hCross hSwapX hSwapY
    exact d.referenceIndexedWitnessAction_allSwapsSafe_visited
      hsat D DS oldRaw hRawPhi hRawReverse rhoS hRawInvariant
      P hPLabel (Classical.choose hGood) (Classical.choose_spec hGood)
      hConst hPColour K hK rho iota refGauge hcls M hOne hMul
      hDiagM occupied hFixed proj cls hSPart hSome hProj
      hProjClass embed hEmbedClass hEmbedAction hEmbedColour
      hVisitedSelected h X Y hCross hSwapX hSwapY
  exact ⟨Theta, hOld, hE, hFEff, hAllSafe⟩

end SemigenericEPPA
