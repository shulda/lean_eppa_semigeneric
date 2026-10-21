import SemigenericEPPA.Bridge.SwappedWitnessOldProjection
import SemigenericEPPA.Bridge.SwappedDifferentOldIndexMiddle
import SemigenericEPPA.Valuations.ReferenceIndexedProjectionAction

/-!
# Different-old-index swapped witness edges are genuinely raw-good

This composes two already certified nontrivial-G positive coherent
flip-safety gates.

(A) For any genuine H-action on the full two-layer valuation witness,
an H-equivariant occupied-only projection of its padded old labels
to true selected old vertices sends a swapped different-old-index
cross edge X↔Y to a genuinely swapped old selected cross pair a↔b.

(B) Exact old gauge-row multipliers from that selected old action
give the SAME noncommutative affine middle for the true selected old
cross-colour and the actual swapped witness effective cross-colour.

The present theorem identifies projected a,b with their fixed old
zero-copy labels in the padded base, transports their raw colours
and old gauge rows, and concludes that the genuinely swapped witness
colour admits a self-reversing raw representative. The conclusion
holds for arbitrary h∈H (not just involutions), arbitrary nonabelian
G, and affine reversal s with s(1) possibly nontrivial.

No false global projection from unoccupied E-classes is assumed.
The required occupied-only projection and selected old raw-colour
preservation are explicit premises, produced later by the factorial
replicated old-fibre action.
-/

namespace SemigenericEPPA

universe u v w t q

variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w}
variable {V : Type t} {S : Type q}
variable {d : RawDatum G C}

namespace EffectiveGeometry

/-- On the TRUE reference-indexed valuation group action, an
actually swapped witness cross-edge with different original E-part
indices is raw-good whenever its old padded labels have the
canonical occupied-only equivariant projection onto a selected raw
H-structure and M is the actual selected-old gauge multiplier.

The full witness remains fixed; only the action and selected old
projection depend on S and H. -/
theorem good_swappedDifferentOldIndex_of_selectedProjection
    (D : EffectiveGeometry d.s V)
    (DS : EffectiveGeometry d.s S)
    (oldRaw : S → S → C)
    (hRawPhi : ∀ a b : S, ¬DS.part a b →
      d.phi (oldRaw a b) = DS.F a b)
    (hRawReverse : ∀ a b : S, ¬DS.part a b →
      oldRaw b a = d.reverse (oldRaw a b))
    (rhoS : H →* Equiv.Perm S)
    (hRawInvariant : ∀ (h : H) (a b : S), ¬DS.part a b →
      oldRaw (rhoS h a) (rhoS h b) = oldRaw a b)
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
    (hRow : ∀ (h : H) (a : S) (j : Quotient D.part),
      P.vertexGauge (rho h (embed a)) (iota h j) =
        M h (Quotient.mk D.part (embed a)) j *
          P.vertexGauge (embed a) j)
    (hsat : d.IsCongruenceSaturated)
    (h : H) (X Y : EffectiveWitnessVertex D)
    (hDifferent : X.part.1 ≠ Y.part.1)
    (hSwapX : D.referenceIndexedWitnessAction
      rho iota z hcls M hOne hMul h X = Y)
    (hSwapY : D.referenceIndexedWitnessAction
      rho iota z hcls M hOne hMul h Y = X) :
    K.toEffectiveGeometry.F X Y ∈ d.selfReverseEffective := by
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
  have hRawOldSwap : oldRaw b a = oldRaw a b := by
    have hr := hRawInvariant h a b hab
    rw [hSwapA, hSwapB] at hr
    exact hr
  have hRawFixed : d.reverse (oldRaw a b) = oldRaw a b := by
    calc
      d.reverse (oldRaw a b) = oldRaw b a :=
        (hRawReverse a b hab).symm
      _ = oldRaw a b := hRawOldSwap
  have hOldGood :
      D.F (embed a) (embed b) ∈ d.selfReverseEffective := by
    refine ⟨oldRaw a b, ?_, hRawFixed⟩
    calc
      d.phi (oldRaw a b) = DS.F a b := hRawPhi a b hab
      _ = D.F (embed a) (embed b) :=
        (hEmbedColour a b hab).symm
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
    d.good_of_swappedWitness_projectedOldMiddle
      hsat D P hPLabel g0 hPConstant hPColour
      rho iota hcls M K hK sigma hcompat h X Y
      hParts hWitnessSwapX hWitnessSwapY
      (embed a) (embed b)
      hEmbedCross hIndexA hIndexB
      hSwapEmbedA hSwapEmbedB
      (hRow h a (Quotient.mk D.part (embed b)))
      hOldGood
  exact hGood

end EffectiveGeometry

end SemigenericEPPA
