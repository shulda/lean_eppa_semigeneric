import SemigenericEPPA.Structure.OnePointRawAmalgam

/-!
# Exact raw restrictions and the full one-point RAW amalgam

The effective one-point strong amalgam already preserves both
one-point effective geometries. The raw prescription from both
one-point sides preserves each cross-part prescribed raw edge.
If the raw sides agree on their old common carrier, the *completed*
raw colouring reproduces every old side colour EXACTLY, including
absence of colours on E-related pairs.

This packages a genuine strong one-point amalgamation theorem in
the literal relational language L_C. An explicit linear order on
the strong carrier is a parameter of the raw-fibre choice.
The reduction to arbitrary finite strong amalgamation and removing
this auxiliary order are separate tasks.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}
variable {D : EffectiveGeometry d.s V}
variable {L R : OnePointEffectiveExtension D}
variable (A : OnePointRawColouring (d := d) D L)
variable (B : OnePointRawColouring (d := d) D R)

/-- The joint prescription restricts exactly to the first input side. -/
theorem combinedOnePointRaw_first
    (x y : Option V) :
    combinedOnePointRaw A B (firstOnePoint x) (firstOnePoint y) =
      A.colour x y := by
  cases x <;> cases y <;> rfl

/-- If the two old substructures have the same raw colours, the
joint prescription also restricts exactly to the second input. -/
theorem combinedOnePointRaw_second
    (hAgree : AgreeOnOldRaw A B) (x y : Option V) :
    combinedOnePointRaw A B (secondOnePoint x) (secondOnePoint y) =
      B.colour x y := by
  cases x with
  | none =>
    cases y <;> rfl
  | some a =>
    cases y with
    | none => rfl
    | some b => exact hAgree a b

section Completion

variable [LinearOrder (TwoPointCarrier V)]

/-- Any already prescribed raw cross-edge is literally retained by
the total raw completion. -/
private theorem completion_preserves
    (x y : TwoPointCarrier V) (c : C)
    (hc : combinedOnePointRaw A B x y = some c) :
    (rawOnePointExtension A B).toPresentation.colour x y = some c := by
  change d.completeRaw
      (effectiveOnePointAmalgam D L R).part
      (combinedOnePointRaw A B)
      (effectiveOnePointAmalgam D L R).F x y = some c
  exact d.completeRaw_prescribed
    (effectiveOnePointAmalgam D L R).part
    (effectiveOnePointAmalgam D L R).part.iseqv
    (combinedOnePointRaw A B)
    (effectiveOnePointAmalgam D L R).F
    (combinedOnePointRaw_same A B)
    (combinedOnePointRaw_reverse A B)
    x y c hc

/-- No completed raw colour is present on an E-related pair. -/
private theorem completion_none_of_part
    (x y : TwoPointCarrier V)
    (hE : (effectiveOnePointAmalgam D L R).part x y) :
    (rawOnePointExtension A B).toPresentation.colour x y = none := by
  change d.completeRaw
      (effectiveOnePointAmalgam D L R).part
      (combinedOnePointRaw A B)
      (effectiveOnePointAmalgam D L R).F x y = none
  exact d.completeRaw_same
    (effectiveOnePointAmalgam D L R).part
    (combinedOnePointRaw A B)
    (effectiveOnePointAmalgam D L R).F x y hE

/-- The completed colouring is IDENTICAL on the first one-point
substructure, not merely compatible with its effective colours. -/
theorem completedRaw_first_exact
    (x y : Option V) :
    (rawOnePointExtension A B).toPresentation.colour
        (firstOnePoint x) (firstOnePoint y) = A.colour x y := by
  cases hc : A.colour x y with
  | none =>
    rw [hc]
    have hE : L.geometry.part x y := (A.none_iff x y).1 hc
    exact completion_none_of_part A B (firstOnePoint x) (firstOnePoint y)
      ((effectiveOnePointAmalgam_first_part D L R x y).2 hE)
  | some c =>
    rw [hc]
    exact completion_preserves A B (firstOnePoint x) (firstOnePoint y) c
      (by rw [combinedOnePointRaw_first A B x y]; exact hc)

/-- The completed colouring is likewise IDENTICAL on the second
one-point substructure whenever they agree on the common base. -/
theorem completedRaw_second_exact
    (hAgree : AgreeOnOldRaw A B) (x y : Option V) :
    (rawOnePointExtension A B).toPresentation.colour
        (secondOnePoint x) (secondOnePoint y) = B.colour x y := by
  cases hc : B.colour x y with
  | none =>
    rw [hc]
    have hE : R.geometry.part x y := (B.none_iff x y).1 hc
    exact completion_none_of_part A B (secondOnePoint x) (secondOnePoint y)
      ((effectiveOnePointAmalgam_second_part D L R x y).2 hE)
  | some c =>
    rw [hc]
    exact completion_preserves A B (secondOnePoint x) (secondOnePoint y) c
      (by rw [combinedOnePointRaw_second A B hAgree x y]; exact hc)

/-- All literal P_c relations on the first side are preserved
AND reflected by the strong raw amalgam. -/
theorem rawOnePoint_first_raw_exact
    (c : C) (x y : Option V) :
    rawRel (rawOnePointExtension A B).toStructure c
        (firstOnePoint x) (firstOnePoint y) ↔
      A.colour x y = some c := by
  change
    (rawOnePointExtension A B).toPresentation.colour
        (firstOnePoint x) (firstOnePoint y) = some c ↔
      A.colour x y = some c
  rw [completedRaw_first_exact A B x y]

/-- All literal P_c relations on the second side are preserved
AND reflected, independently of any choice on the new-new edge. -/
theorem rawOnePoint_second_raw_exact
    (hAgree : AgreeOnOldRaw A B) (c : C) (x y : Option V) :
    rawRel (rawOnePointExtension A B).toStructure c
        (secondOnePoint x) (secondOnePoint y) ↔
      B.colour x y = some c := by
  change
    (rawOnePointExtension A B).toPresentation.colour
        (secondOnePoint x) (secondOnePoint y) = some c ↔
      B.colour x y = some c
  rw [completedRaw_second_exact A B hAgree x y]

/-- STRONG one-point amalgamation of complete raw E-rectangle
colourings with matching common base: one genuine R1--R3
structure on V ⊕ Bool, exact induced restrictions of both E and
every raw P_c, and two distinct new vertices by construction.

The auxiliary linear order is explicit, to be supplied for a
finite carrier in the general finite-SAP theorem. -/
theorem raw_onePoint_strong_amalgamation
    (hAgree : AgreeOnOldRaw A B) :
    ∃ S : Structure (rectangleLanguage C) (TwoPointCarrier V),
      IsRectangleStructure d S ∧
      (∀ x y : Option V,
        partRel S (firstOnePoint x) (firstOnePoint y) ↔
          L.geometry.part x y) ∧
      (∀ x y : Option V,
        partRel S (secondOnePoint x) (secondOnePoint y) ↔
          R.geometry.part x y) ∧
      (∀ c : C, ∀ x y : Option V,
        rawRel S c (firstOnePoint x) (firstOnePoint y) ↔
          A.colour x y = some c) ∧
      (∀ c : C, ∀ x y : Option V,
        rawRel S c (secondOnePoint x) (secondOnePoint y) ↔
          B.colour x y = some c) := by
  let W := rawOnePointExtension A B
  refine ⟨W.toStructure, W.toStructure_isRectangleStructure,
    ?_, ?_, ?_, ?_⟩
  · intro x y
    exact (W.toStructure_part (firstOnePoint x) (firstOnePoint y)).trans
      (effectiveOnePointAmalgam_first_part D L R x y)
  · intro x y
    exact (W.toStructure_part (secondOnePoint x) (secondOnePoint y)).trans
      (effectiveOnePointAmalgam_second_part D L R x y)
  · intro c x y
    exact rawOnePoint_first_raw_exact A B c x y
  · intro c x y
    exact rawOnePoint_second_raw_exact A B hAgree c x y

end Completion
end SemigenericEPPA
