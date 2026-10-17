import SemigenericEPPA.Structure.OnePointEffectiveAmalgam
import SemigenericEPPA.Structure.EffectiveRawExtension

/-!
# Raw-colour gluing over the verified effective one-point SAP

Two one-point effective extensions over a common old geometry are
amalgamated by the already-certified effectiveOnePointAmalgam.

If they carry complete reversible raw colours compatible with the
effective colours and agreeing on the old common carrier, we may
prescribe ALL the raw edges from both sides simultaneously on
V ⊕ Bool, leaving only the previously absent new-new edge unspecified.

This module proves that the combined prescription is:
* blank on E-related pairs;
* reversal-equivariant;
* compatible with the EFFECTIVE COLOURS OF THE GLOBAL AMALGAM.

Consequently the existing EffectiveRawExtension theorem constructs
a genuine full R1--R3 raw structure. At this stage the exact equality
of the induced raw substructures is a separate proof obligation.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}

/-- A complete raw colouring on a one-point effective extension.
No synthetic axiom about the raw fibres is used: each present colour
must map to the exact prescribed effective colour. -/
structure OnePointRawColouring
    (D : EffectiveGeometry d.s V) (L : OnePointEffectiveExtension D) where
  colour : Option V → Option V → Option C
  none_iff : ∀ x y, colour x y = none ↔ L.geometry.part x y
  reverse : ∀ x y,
    colour y x = Option.map d.reverse (colour x y)
  projects : ∀ x y c, colour x y = some c →
    d.phi c = L.geometry.F x y

namespace OnePointRawColouring

variable {D : EffectiveGeometry d.s V}
variable {L : OnePointEffectiveExtension D}

/-- Every present raw colour is on a cross-part ordered pair. -/
theorem cross_of_colour
    (A : OnePointRawColouring (d := d) D L)
    (x y : Option V) (c : C) (hc : A.colour x y = some c) :
    ¬L.geometry.part x y := by
  intro hE
  have hn := (A.none_iff x y).2 hE
  rw [hc] at hn
  cases hn

end OnePointRawColouring

/-- Prescribe ALL side edges on the common strong carrier. The
new-new edge (in both orientations) is left unspecified; the raw
completion lemma will supply an allowed representative if cross-part. -/
def combinedOnePointRaw
    {D : EffectiveGeometry d.s V}
    {L R : OnePointEffectiveExtension D}
    (A : OnePointRawColouring (d := d) D L)
    (B : OnePointRawColouring (d := d) D R) :
    TwoPointCarrier V → TwoPointCarrier V → Option C
  | Sum.inl x, Sum.inl y => A.colour (some x) (some y)
  | Sum.inl x, Sum.inr false => A.colour (some x) none
  | Sum.inl x, Sum.inr true => B.colour (some x) none
  | Sum.inr false, Sum.inl y => A.colour none (some y)
  | Sum.inr true, Sum.inl y => B.colour none (some y)
  | Sum.inr _, Sum.inr _ => none

/-- All old-old prescriptions are unambiguous because the two raw
one-point structures agree on the common old carrier. -/
def AgreeOnOldRaw
    {D : EffectiveGeometry d.s V}
    {L R : OnePointEffectiveExtension D}
    (A : OnePointRawColouring (d := d) D L)
    (B : OnePointRawColouring (d := d) D R) : Prop :=
  ∀ x y : V, A.colour (some x) (some y) = B.colour (some x) (some y)

/-- The partial colouring vanishes on every amalgamated E-pair.
The two distinct new vertices are left uncoloured regardless of
whether they attach to the same old E-part. -/
theorem combinedOnePointRaw_same
    {D : EffectiveGeometry d.s V}
    {L R : OnePointEffectiveExtension D}
    (A : OnePointRawColouring (d := d) D L)
    (B : OnePointRawColouring (d := d) D R)
    (x y : TwoPointCarrier V)
    (hE : (effectiveOnePointAmalgam D L R).part x y) :
    combinedOnePointRaw A B x y = none := by
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      exact (A.none_iff (some a) (some b)).2
        ((effectiveOnePointAmalgam_first_part D L R (some a) (some b)).1 hE)
    | inr side =>
      cases side with
      | false =>
        exact (A.none_iff (some a) none).2
          ((effectiveOnePointAmalgam_first_part D L R (some a) none).1 hE)
      | true =>
        exact (B.none_iff (some a) none).2
          ((effectiveOnePointAmalgam_second_part D L R (some a) none).1 hE)
  | inr side =>
    cases side with
    | false =>
      cases y with
      | inl b =>
        exact (A.none_iff none (some b)).2
          ((effectiveOnePointAmalgam_first_part D L R none (some b)).1 hE)
      | inr _ =>
        rfl
    | true =>
      cases y with
      | inl b =>
        exact (B.none_iff none (some b)).2
          ((effectiveOnePointAmalgam_second_part D L R none (some b)).1 hE)
      | inr _ =>
        rfl

/-- The two one-point raw involutions assemble exactly. -/
theorem combinedOnePointRaw_reverse
    {D : EffectiveGeometry d.s V}
    {L R : OnePointEffectiveExtension D}
    (A : OnePointRawColouring (d := d) D L)
    (B : OnePointRawColouring (d := d) D R)
    (x y : TwoPointCarrier V) :
    combinedOnePointRaw A B y x =
      Option.map d.reverse (combinedOnePointRaw A B x y) := by
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      exact A.reverse (some a) (some b)
    | inr side =>
      cases side with
      | false => exact A.reverse (some a) none
      | true => exact B.reverse (some a) none
  | inr side =>
    cases side with
    | false =>
      cases y with
      | inl b => exact A.reverse none (some b)
      | inr _ => rfl
    | true =>
      cases y with
      | inl b => exact B.reverse none (some b)
      | inr _ => rfl

/-- Every combined prescribed edge has EXACTLY the effective colour
assigned by the global, already-verified effective amalgam.
No new-new edge is pre-coloured, so the two-source data never conflict. -/
theorem combinedOnePointRaw_projects
    {D : EffectiveGeometry d.s V}
    {L R : OnePointEffectiveExtension D}
    (A : OnePointRawColouring (d := d) D L)
    (B : OnePointRawColouring (d := d) D R)
    (x y : TwoPointCarrier V) (c : C)
    (hc : combinedOnePointRaw A B x y = some c) :
    d.phi c = (effectiveOnePointAmalgam D L R).F x y := by
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have hside : A.colour (some a) (some b) = some c := hc
      have hcross := A.cross_of_colour (some a) (some b) c hside
      calc
        d.phi c = L.geometry.F (some a) (some b) :=
          A.projects (some a) (some b) c hside
        _ = (effectiveOnePointAmalgam D L R).F
              (firstOnePoint (some a)) (firstOnePoint (some b)) :=
          (effectiveOnePointAmalgam_first_cross D L R
            (some a) (some b) hcross).symm
    | inr side =>
      cases side with
      | false =>
        have hside : A.colour (some a) none = some c := hc
        have hcross := A.cross_of_colour (some a) none c hside
        calc
          d.phi c = L.geometry.F (some a) none :=
            A.projects (some a) none c hside
          _ = (effectiveOnePointAmalgam D L R).F
              (firstOnePoint (some a)) (firstOnePoint none) :=
            (effectiveOnePointAmalgam_first_cross D L R
              (some a) none hcross).symm
      | true =>
        have hside : B.colour (some a) none = some c := hc
        have hcross := B.cross_of_colour (some a) none c hside
        calc
          d.phi c = R.geometry.F (some a) none :=
            B.projects (some a) none c hside
          _ = (effectiveOnePointAmalgam D L R).F
              (secondOnePoint (some a)) (secondOnePoint none) :=
            (effectiveOnePointAmalgam_second_cross D L R
              (some a) none hcross).symm
  | inr side =>
    cases side with
    | false =>
      cases y with
      | inl b =>
        have hside : A.colour none (some b) = some c := hc
        have hcross := A.cross_of_colour none (some b) c hside
        calc
          d.phi c = L.geometry.F none (some b) :=
            A.projects none (some b) c hside
          _ = (effectiveOnePointAmalgam D L R).F
              (firstOnePoint none) (firstOnePoint (some b)) :=
            (effectiveOnePointAmalgam_first_cross D L R
              none (some b) hcross).symm
      | inr _ =>
        cases hc
    | true =>
      cases y with
      | inl b =>
        have hside : B.colour none (some b) = some c := hc
        have hcross := B.cross_of_colour none (some b) c hside
        calc
          d.phi c = R.geometry.F none (some b) :=
            B.projects none (some b) c hside
          _ = (effectiveOnePointAmalgam D L R).F
              (secondOnePoint none) (secondOnePoint (some b)) :=
            (effectiveOnePointAmalgam_second_cross D L R
              none (some b) hcross).symm
      | inr _ =>
        cases hc

/-- The verified raw-fibre construction now applies to the FULL
effective one-point amalgam with the side edges prescribed. -/
noncomputable def rawOnePointExtension
    {D : EffectiveGeometry d.s V}
    {L R : OnePointEffectiveExtension D}
    (A : OnePointRawColouring (d := d) D L)
    (B : OnePointRawColouring (d := d) D R)
    [LinearOrder (TwoPointCarrier V)] :
    EffectiveRawExtension d (TwoPointCarrier V) where
  part := (effectiveOnePointAmalgam D L R).part
  effective := (effectiveOnePointAmalgam D L R).F
  prescribed := combinedOnePointRaw A B
  prescribed_same := combinedOnePointRaw_same A B
  prescribed_reverse := combinedOnePointRaw_reverse A B
  prescribed_effective := combinedOnePointRaw_projects A B
  effective_reverse := (effectiveOnePointAmalgam D L R).reverse_cross
  effective_rectangle := (effectiveOnePointAmalgam D L R).rectangle

/-- A genuine raw R1--R3 structure exists on the strong carrier.
Exact side embeddings and the finite strong-amalgamation reduction
are next steps, not assumed by this statement. -/
theorem rawOnePointExtension_isRectangleStructure
    {D : EffectiveGeometry d.s V}
    {L R : OnePointEffectiveExtension D}
    (A : OnePointRawColouring (d := d) D L)
    (B : OnePointRawColouring (d := d) D R)
    [LinearOrder (TwoPointCarrier V)] :
    IsRectangleStructure d (rawOnePointExtension A B).toStructure :=
  (rawOnePointExtension A B).toStructure_isRectangleStructure

end SemigenericEPPA
