import SemigenericEPPA.Structure.FixedJointRawCover
import SemigenericEPPA.Structure.TotalOldRawPalette

/-!
# Apply ONE fixed joint raw cover directly to old-substructure H-actions

The certified FixedJointRawCover stores a group-lift API requiring an
H-invariant total raw reference on an H-invariant selected subset
of the effective base. In the coherent EPPA application these
conditions are NOT additional assumptions: the selected set is
exactly ψ(S), where ψ is the one fixed old embedding and H acts
on S by genuine old raw automorphisms.

This lemma proves the missing translation. An old H-action on S
preserving the actual old E relation and all raw ordered colours,
and an effective H-action Theta on the common witness B extending
that action on ψ(S), automatically give the correct invariance
of the prechosen old raw reference, despite its arbitrary values
outside the old image.

Therefore, assuming only that the effective H-action is safe on
its swapped cross-E edges, the EXISTING SAME fixed joint raw cover
has a strict homomorphic raw-automorphism lift preserving every
original raw zero-section vertex of S exactly.

The proof does NOT choose a new raw code, baseline, carrier, or
raw cover after S/H. It does not claim that raw flip-safety follows
from effective invariance; the latter remains a geometric gate
handled separately by the affine same/different-index arguments.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {C : Type w} {U : Type z} {V : Type t}
variable {d : RawDatum G C}

/-- A genuine raw automorphism group action on an induced old
subset S lifts homomorphically to the SAME prechosen joint
raw cover, whenever the corresponding effective witness action
is safe on every exchanged cross-E pair. The raw-reference and
selected-image invariance conditions needed by the universal
cover API are DERIVED, not postulated. -/
theorem FixedJointRawCover.exists_rawGroupLift_of_selectedRawAction
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (e : U → V)
    (J : FixedJointRawCover P D e)
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
    ∃ lift : H →* Equiv.Perm
        (RawCoverVertex V (UniversalResidualCarrier C)),
      (∀ (h : H) (x : S),
        lift h
          (e x.val, fun _ : V => (0 : UniversalResidualCarrier C)) =
          (e (rhoS h x).val,
            fun _ : V => (0 : UniversalResidualCarrier C))) ∧
      (∀ (h : H)
        (X Y : RawCoverVertex V (UniversalResidualCarrier C)),
        D.part (lift h X).1 (lift h Y).1 ↔ D.part X.1 Y.1) ∧
      (∀ (h : H) (c : C)
        (X Y : RawCoverVertex V (UniversalResidualCarrier C)),
        rawRel (rawCoverPresentation D J.code J.baseline
          J.baseline_reverse).toStructure c
          (lift h X) (lift h Y) ↔
        rawRel (rawCoverPresentation D J.code J.baseline
          J.baseline_reverse).toStructure c X Y) := by
  let T : Set V := Set.range (fun x : S => e x.val)
  have hSubset : T ⊆ Set.range e := by
    intro v hv
    obtain ⟨x, hx⟩ := hv
    exact ⟨x.val, hx⟩
  have hStable : ∀ (h : H) (v : V), v ∈ T → Theta h v ∈ T := by
    intro h v hv
    obtain ⟨x, hx⟩ := hv
    refine ⟨rhoS h x, ?_⟩
    calc
      e (rhoS h x).val = Theta h (e x.val) := (hOld h x).symm
      _ = Theta h v := congrArg (Theta h) hx
  have hReference :
      ∀ (h : H) (x y : V), x ∈ T → y ∈ T →
      ¬D.part x y →
      oldRawReferenceOnBase P e J.defaultColour
        (Theta h x) (Theta h y) =
        oldRawReferenceOnBase P e J.defaultColour x y := by
    intro h x y hx hy hxy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    subst x
    subst y
    have hab : ¬P.part a.val b.val := by
      intro hp
      exact hxy ((hPartEmbed a.val b.val).mpr hp)
    have hnewcross :
        ¬P.part (rhoS h a).val (rhoS h b).val := by
      intro hp
      exact hab ((hPartOld h a b).mp hp)
    have hNew := P.totalOldRawColour_cross
      (rhoS h a).val (rhoS h b).val hnewcross
    have hOldColour := P.totalOldRawColour_cross
      a.val b.val hab
    have hTotal :
        P.totalOldRawColour (rhoS h a).val (rhoS h b).val =
          P.totalOldRawColour a.val b.val := by
      rw [hColourOld h a b] at hNew
      exact Option.some.inj (hNew.symm.trans hOldColour)
    calc
      oldRawReferenceOnBase P e J.defaultColour
          (Theta h (e a.val)) (Theta h (e b.val)) =
        oldRawReferenceOnBase P e J.defaultColour
          (e (rhoS h a).val) (e (rhoS h b).val) := by
            rw [hOld h a, hOld h b]
      _ = P.totalOldRawColour (rhoS h a).val (rhoS h b).val :=
        oldRawReferenceOnBase_old P e he J.defaultColour
          (rhoS h a).val (rhoS h b).val
      _ = P.totalOldRawColour a.val b.val := hTotal
      _ = oldRawReferenceOnBase P e J.defaultColour
          (e a.val) (e b.val) :=
        (oldRawReferenceOnBase_old P e he J.defaultColour
          a.val b.val).symm
  have hSafeNew : ∀ (h : H) (x y : V),
      ¬D.part x y → ¬(x ∈ T ∧ y ∈ T) →
      Theta h x = y → Theta h y = x →
        ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c := by
    intro h x y hxy _ hswapx hswapy
    exact hFlip h x y hxy hswapx hswapy
  obtain ⟨lift, hLiftOld, hLiftPart, hLiftRaw⟩ :=
    J.safe_groups H Theta T hSubset
      hThetaPart hThetaColour hStable hReference hSafeNew
  refine ⟨lift, ?_, hLiftPart, hLiftRaw⟩
  intro h x
  have hx : e x.val ∈ T := ⟨x, rfl⟩
  calc
    lift h
        (e x.val, fun _ : V => (0 : UniversalResidualCarrier C)) =
      (Theta h (e x.val), fun _ : V =>
        (0 : UniversalResidualCarrier C)) :=
          hLiftOld h (e x.val) hx
    _ = (e (rhoS h x).val, fun _ : V =>
          (0 : UniversalResidualCarrier C)) := by rw [hOld h x]

end SemigenericEPPA
