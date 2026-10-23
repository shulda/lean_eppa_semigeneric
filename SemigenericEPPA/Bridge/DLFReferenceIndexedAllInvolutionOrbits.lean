import SemigenericEPPA.Bridge.DLFSwappedDifferentIndexLocalOrbit
import SemigenericEPPA.Bridge.DLFSwappedSameIndexCompleteOrbit

/-!
# Full TWO-LAYER H-action: involution swapped edges stay in good orbits

For the actual canonical reference-indexed two-layer valuation
action, combine its genuinely exchanged old-index cases:
* same original E-index: the exact diagonal multiplier is 1 and
  the swapped colour lies in the orbit of the chosen good seed;
* different original E-indices: the occupied-only equivariant
  projection yields a truly swapped old pair, and the certified
  visited-column old-row formula gives an exact common affine
  middle, transporting its complete good orbit to the witness.

Only involutions h with h²=1 need the old orbit-safety hypothesis.
No global congruence saturation, no commutativity, no s(1)=1, and
no false row transport on unused columns.

This is the central effective colour-safety interface for the
relative regular-phase DLF construction, which treats non-involutive
old-sector swaps directly using old raw colour invariance.
-/

namespace SemigenericEPPA

universe u v w t q
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w}
variable {V : Type t} {S : Type q}

/-- All actual cross-witness swaps by an H-involution lie in
complete good affine congruence orbits under precisely the
occupied projection and visited old multiplier assumptions. -/
theorem RawDatum.referenceIndexedWitnessAction_involutionCompleteGoodOrbit_visited
    (d : RawDatum G C)
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
    (g0 : G) (hGoodOrbit : d.GoodCompleteOrbitAt g0)
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
    (hVisitedRow : ∀ (h : H) (a : S) (j : Quotient D.part),
      (∃ b : S, cls b = j) →
      P.vertexGauge (rho h (embed a)) (iota h j) =
        M h (Quotient.mk D.part (embed a)) j *
          P.vertexGauge (embed a) j) :
    ∀ (h : H), h * h = 1 →
      ∀ (X Y : EffectiveWitnessVertex D),
      ¬K.toEffectiveGeometry.part X Y →
      D.referenceIndexedWitnessAction
        rho iota z hcls M hOne hMul h X = Y →
      D.referenceIndexedWitnessAction
        rho iota z hcls M hOne hMul h Y = X →
      d.GoodCompleteOrbitAt (K.toEffectiveGeometry.F X Y) := by
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
  intro h htwo X Y hCross hSwapX hSwapY
  have hParts : X.part ≠ Y.part := by
    intro heq
    exact hCross ((K.witness_part_iff X Y).mpr heq)
  have hGoodColour :
      d.GoodCompleteOrbitAt (K.toEffectiveGeometry.F X Y) := by
    by_cases hSame : X.part.1 = Y.part.1
    · exact d.completeGoodOrbitAt_of_swappedWitness_sameOldIndex
        g0 hGoodOrbit D K hK sigma rho hcompat
        (fun k q r => M k q.1 r.1)
        hDiagonalParts h X Y hParts hSame
        hSwapX hSwapY
    · exact D.completeGoodOrbitAt_swappedDifferentOldIndex_of_selectedProjection_visited
        DS rhoS hOldInvolSafe
        P hPLabel g0 hPConstant hPColour K hK
        rho iota z hcls M hOne hMul
        occupied hFixed proj cls hSPart hSome hProj
        hProjClass embed hEmbedClass hEmbedAction hEmbedColour
        hVisitedRow h htwo X Y hSame hSwapX hSwapY
  exact hGoodColour

end SemigenericEPPA
