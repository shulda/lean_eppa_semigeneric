import SemigenericEPPA.Bridge.DLFSwappedWitnessCommonMiddleOrbit
import SemigenericEPPA.Bridge.SwappedDifferentOldIndexRawGoodVisited

/-!
# Actual different-index swapped witness colours inherit one good orbit

The verified occupied equivariant projection sends a real swapped
two-layer witness cross edge to a selected old pair swapped by the
same actual H-element. If this element is an involution, assume
the old pair's effective colour lies in a complete good affine
congruence orbit. The same genuinely visited old gauge-row
equation and exact noncommutative common-middle transport as
coherent EPPA then place the WITNESS colour in that orbit.

No global good-set saturation and no invariance of unrelated
raw colours are required. The actual valuation witness action,
old-index projection and multiplier data are not replaced.
-/

namespace SemigenericEPPA

universe u v w t q
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w}
variable {V : Type t} {S : Type q}
variable {d : RawDatum G C}
namespace EffectiveGeometry

/-- An involution-swapped different-index witness pair inherits
the complete good orbit of a genuinely swapped old pair. -/
theorem completeGoodOrbitAt_swappedDifferentOldIndex_of_selectedProjection_visited
    (D : EffectiveGeometry d.s V)
    (DS : EffectiveGeometry d.s S)
    (rhoS : H →* Equiv.Perm S)
    (hOldInvolSafe : ∀ (h : H), h * h = 1 →
      ∀ (a b : S), ¬DS.part a b →
        rhoS h a = b → rhoS h b = a →
          d.GoodCompleteOrbitAt (DS.F a b))
    (P : IndexedGauge d.s V (Quotient D.part))
    (hPLabel : ∀ w : V,
      P.label w = Quotient.mk D.part w)
    (g0 : G)
    (hPConstant : ∀ i j : Quotient D.part,
      P.skeleton i j = g0)
    (hPColour : ∀ x y : V, ¬D.part x y →
      P.effective x y = D.F x y)
    (K : EffectiveWitnessSkeleton D)
    (hK : ∀ q r : EffectiveWitnessPart D,
      K.colour q r = g0)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (hcls : ∀ (h : H) (w : V),
      Quotient.mk D.part (rho h w) =
        iota h (Quotient.mk D.part w))
    (M : H → Quotient D.part → Quotient D.part → G)
    (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
    (hMul : ∀ (k h : H) (i j : Quotient D.part),
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j)
    (occupied : Quotient D.part → Prop)
    (hFixed : ∀ (h : H) (i : Quotient D.part),
      ¬occupied i → iota h i = i)
    (proj : V → Option S)
    (cls : S → Quotient D.part)
    (hSPart : ∀ a b : S,
      DS.part a b ↔ cls a = cls b)
    (hSome : ∀ (w : V),
      occupied (Quotient.mk D.part w) →
        ∃ a : S, proj w = some a)
    (hProj : ∀ (h : H) (w : V),
      proj (rho h w) = Option.map (rhoS h) (proj w))
    (hProjClass : ∀ (w : V) (a : S),
      proj w = some a → Quotient.mk D.part w = cls a)
    (embed : S → V)
    (hEmbedClass : ∀ a : S,
      Quotient.mk D.part (embed a) = cls a)
    (hEmbedAction : ∀ (h : H) (a : S),
      rho h (embed a) = embed (rhoS h a))
    (hEmbedColour : ∀ a b : S, ¬DS.part a b →
      D.F (embed a) (embed b) = DS.F a b)
    (hVisitedRow : ∀ (h : H) (a : S) (j : Quotient D.part),
      (∃ b : S, cls b = j) →
      P.vertexGauge (rho h (embed a)) (iota h j) =
        M h (Quotient.mk D.part (embed a)) j *
          P.vertexGauge (embed a) j)
    (h : H) (htwo : h * h = 1) (X Y : EffectiveWitnessVertex D)
    (hDifferent : X.part.1 ≠ Y.part.1)
    (hSwapX : D.referenceIndexedWitnessAction
      rho iota z hcls M hOne hMul h X = Y)
    (hSwapY : D.referenceIndexedWitnessAction
      rho iota z hcls M hOne hMul h Y = X) :
    d.GoodCompleteOrbitAt (K.toEffectiveGeometry.F X Y) := by
  let Theta : H →* Equiv.Perm (EffectiveWitnessVertex D) :=
    D.referenceIndexedWitnessAction rho iota z hcls M hOne hMul
  have hThetaOld : ∀ (k : H) (W : EffectiveWitnessVertex D),
      (Theta k W).old = rho k W.old :=
    D.referenceIndexedWitnessAction_oldLabel
      rho iota z hcls M hOne hMul
  have hThetaIndex : ∀ (k : H) (W : EffectiveWitnessVertex D),
      (Theta k W).part.1 = iota k W.part.1 :=
    D.referenceIndexedWitnessAction_oldIndex
      rho iota z hcls M hOne hMul
  obtain ⟨a, b, ha, hb, hab, hSwapA, hSwapB⟩ :=
    exists_swappedOldPair_of_occupiedProjection
      D DS Theta rho iota rhoS cls hSPart
      hThetaOld hThetaIndex occupied hFixed
      proj hSome hProj hProjClass
      h X Y hDifferent hSwapX hSwapY
  have hIndexA : X.part.1 =
      Quotient.mk D.part (embed a) := by
    calc
      X.part.1 = Quotient.mk D.part X.old := X.belongs.symm
      _ = cls a := hProjClass X.old a ha
      _ = Quotient.mk D.part (embed a) := (hEmbedClass a).symm
  have hIndexB : Y.part.1 =
      Quotient.mk D.part (embed b) := by
    calc
      Y.part.1 = Quotient.mk D.part Y.old := Y.belongs.symm
      _ = cls b := hProjClass Y.old b hb
      _ = Quotient.mk D.part (embed b) := (hEmbedClass b).symm
  have hEmbedCross : ¬D.part (embed a) (embed b) := by
    intro hc
    apply hDifferent
    calc
      X.part.1 = Quotient.mk D.part (embed a) := hIndexA
      _ = Quotient.mk D.part (embed b) := Quotient.sound hc
      _ = Y.part.1 := hIndexB.symm
  have hSwapEmbedA : rho h (embed a) = embed b := by
    rw [hEmbedAction h a, hSwapA]
  have hSwapEmbedB : rho h (embed b) = embed a := by
    rw [hEmbedAction h b, hSwapB]
  have hOldGood :
      d.GoodCompleteOrbitAt (D.F (embed a) (embed b)) := by
    have hLocal := hOldInvolSafe h htwo a b hab hSwapA hSwapB
    rw [hEmbedColour a b hab]
    exact hLocal
  have hParts : X.part ≠ Y.part := by
    intro heq
    exact hDifferent (congrArg Prod.fst heq)
  let sigma : H →* Equiv.Perm (EffectiveWitnessPart D) :=
    referenceWitnessPartAction D rho iota z
  have hcompat : ∀ (k : H) (q : EffectiveWitnessPart D)
      (w : V),
      (Quotient.mk D.part (rho k w) = (sigma k q).1) ↔
        (Quotient.mk D.part w = q.1) :=
    referenceWitnessPartAction_fibre_compat D rho iota z hcls
  have hWitnessSwapX :
      witnessCocyclePerm D sigma rho hcompat
        (fun k q r => M k q.1 r.1) h X = Y :=
    hSwapX
  have hWitnessSwapY :
      witnessCocyclePerm D sigma rho hcompat
        (fun k q r => M k q.1 r.1) h Y = X :=
    hSwapY
  obtain ⟨aNew, aOld, middle, _, _, hGood⟩ :=
    d.completeGoodOrbitAt_of_swappedWitness_projectedOldMiddle
      D P hPLabel g0 hPConstant hPColour
      rho iota hcls M K hK sigma hcompat h X Y
      hParts hWitnessSwapX hWitnessSwapY
      (embed a) (embed b)
      hEmbedCross hIndexA hIndexB
      hSwapEmbedA hSwapEmbedB
      (hVisitedRow h a (Quotient.mk D.part (embed b))
        ⟨b, (hEmbedClass b).symm⟩)
      hOldGood
  exact hGood

end EffectiveGeometry
end SemigenericEPPA
