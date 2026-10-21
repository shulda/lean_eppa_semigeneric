import SemigenericEPPA.Bridge.OccupiedProjectionFlipSafety
import SemigenericEPPA.Valuations.EffectiveCarrier

/-!
# Genuine swapped valuation pairs project to swapped selected old pairs

The factorial replicated auxiliary-label action provides a strict
H-equivariant Option-valued projection from its old padded labels
to genuine vertices of the selected induced structure S. There is
no projection on empty old E-classes. Nevertheless a cross-E pair
which is actually swapped by an H-element must be in two occupied
old classes whenever the index action fixes unoccupied indices.

We prove the exact generic transfer for an arbitrary two-layer
valuation-witness H-action Theta which
(1) covers the quotient-index action iota on the FIRST component
    of witness parts (not the valuation function component);
(2) acts on every old padded real label by rho;
(3) fixes the unoccupied quotient indices through iota.

Assuming the genuinely occupied label projection is H-equivariant,
and respects E-classes, every actually swapped witness cross pair
with distinct ORIGINAL old indices projects to a genuinely swapped
cross pair (a,b) in S, with h a=b and h b=a and a not E b.

The argument uses no involution hypothesis on h, works for all
nonabelian effective groups, and requires no global projection
at unoccupied classes. This is the geometric existence gate
needed to instantiate the verified different-old-index affine
common-middle/raw-good theorem.
-/

namespace SemigenericEPPA

universe u v w z
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {V : Type w} {S : Type z}
variable {s : AffineAntiInvolution G}

/-- Swapped cross-witness endpoints project equivariantly to
genuinely swapped old selected endpoints, provided the class-index
actions fix every unoccupied index and every occupied padded label
has a genuine old projection.

The selected old E-relation is represented exactly by equality
of its class map; this permits deriving a genuine old cross-edge. -/
theorem exists_swappedOldPair_of_occupiedProjection
    (D : EffectiveGeometry s V)
    (DS : EffectiveGeometry s S)
    (Theta : H →* Equiv.Perm (EffectiveWitnessVertex D))
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (rhoS : H →* Equiv.Perm S)
    (cls : S → Quotient D.part)
    (hSPart : ∀ a b : S,
      DS.part a b ↔ cls a = cls b)
    (hThetaOld : ∀ (h : H) (X : EffectiveWitnessVertex D),
      (Theta h X).old = rho h X.old)
    (hThetaIndex : ∀ (h : H) (X : EffectiveWitnessVertex D),
      (Theta h X).part.1 = iota h X.part.1)
    (occupied : Quotient D.part → Prop)
    (hFixed : ∀ (h : H) (i : Quotient D.part),
      ¬occupied i → iota h i = i)
    (proj : V → Option S)
    (hSome : ∀ (w : V),
      occupied (Quotient.mk D.part w) →
        ∃ a : S, proj w = some a)
    (hProj : ∀ (h : H) (w : V),
      proj (rho h w) = Option.map (rhoS h) (proj w))
    (hProjClass : ∀ (w : V) (a : S),
      proj w = some a →
        Quotient.mk D.part w = cls a)
    (h : H) (X Y : EffectiveWitnessVertex D)
    (hDifferent : X.part.1 ≠ Y.part.1)
    (hSwapX : Theta h X = Y)
    (hSwapY : Theta h Y = X) :
    ∃ a b : S,
      proj X.old = some a ∧
      proj Y.old = some b ∧
      ¬DS.part a b ∧
      rhoS h a = b ∧
      rhoS h b = a := by
  have hIndex : ∀ (k : H) (Z : EffectiveWitnessVertex D),
      (fun Z : EffectiveWitnessVertex D => Z.part.1) (Theta k Z) =
        iota k ((fun Z : EffectiveWitnessVertex D => Z.part.1) Z) :=
    hThetaIndex
  obtain ⟨hOccX, hOccY⟩ :=
    flippedCrossPart_occupied
      (fun Z : EffectiveWitnessVertex D => Z.part.1)
      Theta iota occupied hIndex hFixed
      h X Y hDifferent hSwapX
  have hOccOldX : occupied (Quotient.mk D.part X.old) := by
    rw [X.belongs]
    exact hOccX
  have hOccOldY : occupied (Quotient.mk D.part Y.old) := by
    rw [Y.belongs]
    exact hOccY
  obtain ⟨a, ha⟩ := hSome X.old hOccOldX
  obtain ⟨b, hb⟩ := hSome Y.old hOccOldY
  have hClassA : cls a = X.part.1 := by
    calc
      cls a = Quotient.mk D.part X.old :=
        (hProjClass X.old a ha).symm
      _ = X.part.1 := X.belongs
  have hClassB : cls b = Y.part.1 := by
    calc
      cls b = Quotient.mk D.part Y.old :=
        (hProjClass Y.old b hb).symm
      _ = Y.part.1 := Y.belongs
  have hCross : ¬DS.part a b := by
    intro hab
    apply hDifferent
    calc
      X.part.1 = cls a := hClassA.symm
      _ = cls b := (hSPart a b).mp hab
      _ = Y.part.1 := hClassB
  have hSwapOldX : rho h X.old = Y.old := by
    calc
      rho h X.old = (Theta h X).old := (hThetaOld h X).symm
      _ = Y.old := congrArg EffectiveWitnessVertex.old hSwapX
  have hSwapOldY : rho h Y.old = X.old := by
    calc
      rho h Y.old = (Theta h Y).old := (hThetaOld h Y).symm
      _ = X.old := congrArg EffectiveWitnessVertex.old hSwapY
  have hOldA : rhoS h a = b := by
    have hs : some (rhoS h a) = some b := by
      calc
        some (rhoS h a) =
            Option.map (rhoS h) (proj X.old) := by rw [ha]; rfl
        _ = proj (rho h X.old) := (hProj h X.old).symm
        _ = proj Y.old := by rw [hSwapOldX]
        _ = some b := hb
    exact Option.some.inj hs
  have hOldB : rhoS h b = a := by
    have hs : some (rhoS h b) = some a := by
      calc
        some (rhoS h b) =
            Option.map (rhoS h) (proj Y.old) := by rw [hb]; rfl
        _ = proj (rho h Y.old) := (hProj h Y.old).symm
        _ = proj X.old := by rw [hSwapOldY]
        _ = some a := ha
    exact Option.some.inj hs
  exact ⟨a, b, ha, hb, hCross, hOldA, hOldB⟩

end SemigenericEPPA
