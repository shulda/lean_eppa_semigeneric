import SemigenericEPPA.Bridge.SwappedSameOldIndexGood
import SemigenericEPPA.Bridge.SwappedDifferentOldIndexRawGood

/-!
# Both actual swapped-edge branches give one raw-safe witness action

For the genuine indexed reference-twisted H-action on the complete
two-layer valuation witness, swapped cross-edges must be handled
according to whether the two distinct witness valuation parts
have equal or different ORIGINAL old E-indices.

* Equal indices: the canonical multiplier M_h(i,i)=1, and the
  verified actual witness swapped-edge formula plus global affine
  congruence saturation makes the edge raw-good.
* Different indices: the occupied-only H-equivariant projection
  and exact old zero-copy gauge-row multiplier transport supply a
  genuinely swapped old selected raw edge with EXACTLY the same
  noncommutative affine middle. Again saturation makes the edge
  raw-good.

This theorem combines the two certified branches into the
EXACT flip-safety condition required by the fixed raw-cover
group-lift lemma, with NO restriction on the order of h.
No additional projection from unused old E-classes is presumed.
All actual group-action compatibility and projected old-colour
hypotheses are explicit; their construction from a finite
factorial old-label action is a separate integration gate.

The conclusion is not only good-set membership: it supplies a
literal raw colour fixed by the raw reversal for every swapped
witness cross-edge.
-/

namespace SemigenericEPPA

universe u v w t q
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w}
variable {V : Type t} {S : Type q}

/-- All genuinely exchanged cross-E edges of the ACTUAL full
indexed witness H-action have a literal self-reversing raw
representative, combining equal and different old quotient indices.

The old H-action is required to preserve raw colours only on the
selected old S, never on all padded old labels. The multiplier
matrix is noncommutative and strict; the only diagonal condition
is M_h(i,i)=1. All pair swaps by arbitrary group elements h are
covered, not just transpositions from order-two elements. -/
theorem RawDatum.referenceIndexedWitnessAction_allSwapsSafe
    (d : RawDatum G C)
    (hsat : d.IsCongruenceSaturated)
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
    (g0 : G) (hGood : g0 ∈ d.selfReverseEffective)
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
    (hDiagonal : ∀ (h : H) (i : Quotient D.part), M h i i = 1)
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
          P.vertexGauge (embed a) j) :
    ∀ (h : H) (X Y : EffectiveWitnessVertex D),
      ¬K.toEffectiveGeometry.part X Y →
      D.referenceIndexedWitnessAction
        rho iota z hcls M hOne hMul h X = Y →
      D.referenceIndexedWitnessAction
        rho iota z hcls M hOne hMul h Y = X →
      ∃ c : C,
        d.phi c = K.toEffectiveGeometry.F X Y ∧
          d.reverse c = c := by
  let sigma : H →* Equiv.Perm (EffectiveWitnessPart D) :=
    referenceWitnessPartAction D rho iota z
  have hcompat : ∀ (h : H) (q : EffectiveWitnessPart D)
      (w : V),
      (Quotient.mk D.part (rho h w) = (sigma h q).1) ↔
        (Quotient.mk D.part w = q.1) :=
    referenceWitnessPartAction_fibre_compat D rho iota z hcls
  have hDiagonalParts :
      ∀ (h : H) (q r : EffectiveWitnessPart D),
        q.1 = r.1 →
          (fun k q r => M k q.1 r.1) h q r = 1 := by
    intro h q r heq
    change M h q.1 r.1 = 1
    rw [← heq]
    exact hDiagonal h q.1
  intro h X Y hCross hSwapX hSwapY
  have hParts : X.part ≠ Y.part := by
    intro heq
    exact hCross ((K.witness_part_iff X Y).mpr heq)
  have hGoodColour :
      K.toEffectiveGeometry.F X Y ∈ d.selfReverseEffective := by
    by_cases hSame : X.part.1 = Y.part.1
    · exact d.good_of_swappedWitness_sameOldIndex
        hsat g0 hGood D K hK sigma rho hcompat
        (fun k q r => M k q.1 r.1)
        hDiagonalParts h X Y hParts hSame
        hSwapX hSwapY
    · exact D.good_swappedDifferentOldIndex_of_selectedProjection
        DS oldRaw hRawPhi hRawReverse rhoS hRawInvariant
        P hPLabel g0 hPConstant hPColour K hK
        rho iota z hcls M hOne hMul
        occupied hFixed proj cls hSPart hSome hProj
        hProjClass embed hEmbedClass hEmbedAction hEmbedColour
        hRow hsat h X Y hSame hSwapX hSwapY
  exact hGoodColour

end SemigenericEPPA
