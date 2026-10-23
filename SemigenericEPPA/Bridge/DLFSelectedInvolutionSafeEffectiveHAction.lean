import SemigenericEPPA.Valuations.SelectedExplicitRelativeEffectiveHAction
import SemigenericEPPA.Bridge.DLFReferenceIndexedAllInvolutionOrbits

/-!
# Genuine full effective H-action safe for all involutions, using ONE good orbit

The coherent-EPPA construction chooses the actual reference-indexed
two-layer H-action from canonical multipliers M and selected reference
gauge z. The certified relative-DLF colour theorem says that all
cross-pairs swapped by an H-INVOLUTION belong to complete good
affine congruence orbits, provided the same M is used, the occupied
old projection is equivariant, and the selected old involutions
are already safe.

Here we combine those two certified ingredients with the SAME
multipliers, reference and fixed skeleton. Unlike the coherent
full-saturation theorem, global IsCongruenceSaturated is never used.
The selected constant good skeleton g0 must itself have a complete
good orbit, and the old action need only be safe for involutions
(as required for the subsequent regular-phase construction).

This is a conditional genuine full effective H-action. It does
not yet choose the fixed factorial witness from an arbitrary
HasCompleteGoodOrbit datum or construct the joint raw cover.
-/

namespace SemigenericEPPA

universe u v w t z
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {H : Type t} [Group H]
variable {S0 : Type z}
variable {d : RawDatum G C}

/-- The SAME explicitly constructed effective group action extends
all selected old vertices and preserves global E/F, while every
cross-witness pair swapped by an H-involution has a complete good
affine congruence orbit.

Neither Theta nor the multiplier matrix nor the reference gauge
is postulated as an independent input. -/
theorem IndexedGauge.exists_selectedInvolutionOrbitSafeEffectiveHAction
    (D : EffectiveGeometry d.s V)
    (P : IndexedGauge d.s V (Quotient D.part))
    (hPLabel : ∀ x : V, P.label x = Quotient.mk D.part x)
    (hPColour : ∀ x y : V, ¬D.part x y →
      P.effective x y = D.F x y)
    (hGood : d.selfReverseEffective.Nonempty)
    (hGoodOrbit : d.GoodCompleteOrbitAt (Classical.choose hGood))
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
    (rhoS : H →* Equiv.Perm S0)
    (hOldInvolSafe : ∀ (h : H), h * h = 1 →
      ∀ (a b : S0), ¬DS.part a b →
        rhoS h a = b → rhoS h b = a →
          d.GoodCompleteOrbitAt (DS.F a b))
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
    (hEmbedMem : ∀ a : S0, embed a ∈ S) :
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
      (∀ (h : H), h * h = 1 →
        ∀ (X Y : EffectiveWitnessVertex D),
          ¬K.toEffectiveGeometry.part X Y →
          Theta h X = Y → Theta h Y = X →
          d.GoodCompleteOrbitAt (K.toEffectiveGeometry.F X Y)) := by
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
  have hAllSafe :
      ∀ (h : H), h * h = 1 →
        ∀ (X Y : EffectiveWitnessVertex D),
          ¬K.toEffectiveGeometry.part X Y →
          Theta h X = Y → Theta h Y = X →
          d.GoodCompleteOrbitAt (K.toEffectiveGeometry.F X Y) := by
    intro h htwo X Y hCross hSwapX hSwapY
    exact d.referenceIndexedWitnessAction_involutionCompleteGoodOrbit_visited
      D DS rhoS hOldInvolSafe
      P hPLabel (Classical.choose hGood) hGoodOrbit
      hConst hPColour K hK rho iota refGauge hcls
      M hOne hMul hDiagM
      occupied hFixed proj cls hSPart hSome hProj
      hProjClass embed hEmbedClass hEmbedAction hEmbedColour
      hVisitedSelected h htwo X Y hCross hSwapX hSwapY
  exact ⟨Theta, hOld, hE, hFEff, hAllSafe⟩

end SemigenericEPPA
