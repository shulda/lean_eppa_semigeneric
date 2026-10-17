import SemigenericEPPA.Structure.OnePointGaugeAttached

/-!
# Global one-point strong amalgamation of effective E-rectangle geometries

The concrete indexed gauge construction combines two arbitrary one-point
extensions of the SAME old effective E-rectangle geometry into one
effective geometry on V ⊕ Bool, with two distinct new vertices.

All cross-part effective colours from BOTH extensions are preserved
EXACTLY, and E is preserved and reflected on each old-plus-one side.
No assumptions on finite carriers, the shape of G or s(1), the
self-reversing raw colour set S, or any EPPA existence theorem.

This is a complete ONE-POINT SAP theorem at the EFFECTIVE level.
To obtain the paper's RAW class SAP, one must still combine the
prescribed raw edge functions and use the verified raw-fibre completion.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- The explicit global effective geometry from the canonical
class-indexed skeleton and the two one-point vertex gauges. -/
noncomputable def effectiveOnePointAmalgam
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D) :
    EffectiveGeometry s (TwoPointCarrier V) :=
  (canonicalOnePointGauge D L R).toEffectiveGeometry

/-- The first one-point extension is reproduced exactly at the
level of the E-equivalence relation. -/
theorem effectiveOnePointAmalgam_first_part
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (x y : Option V) :
    (effectiveOnePointAmalgam D L R).part
        (firstOnePoint x) (firstOnePoint y) ↔
      L.geometry.part x y := by
  exact (canonicalOnePointGauge_part D L R
    (firstOnePoint x) (firstOnePoint y)).trans
    (amalgamPart_first_iff D.part L.toPartExtension R.toPartExtension x y)

/-- The second extension is likewise exactly preserved and reflected. -/
theorem effectiveOnePointAmalgam_second_part
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (x y : Option V) :
    (effectiveOnePointAmalgam D L R).part
        (secondOnePoint x) (secondOnePoint y) ↔
      R.geometry.part x y := by
  exact (canonicalOnePointGauge_part D L R
    (secondOnePoint x) (secondOnePoint y)).trans
    (amalgamPart_second_iff D.part L.toPartExtension R.toPartExtension x y)

/-- All outgoing NEW→OLD effective edges on the first side are
preserved: attached old class and fresh singleton are both covered. -/
theorem effectiveOnePointAmalgam_first_new_old
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (a : V) (hcross : ¬L.geometry.part none (some a)) :
    (effectiveOnePointAmalgam D L R).F
        (firstOnePoint none) (firstOnePoint (some a)) =
      L.geometry.F none (some a) := by
  cases hattach : L.toPartExtension.attachment with
  | none =>
    exact canonicalOnePointGauge_left_fresh_old D L R hattach a
  | some i =>
    exact canonicalOnePointGauge_left_attached_old
      D L R i hattach a hcross

/-- The symmetric NEW→OLD preservation on the right side. -/
theorem effectiveOnePointAmalgam_second_new_old
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (a : V) (hcross : ¬R.geometry.part none (some a)) :
    (effectiveOnePointAmalgam D L R).F
        (secondOnePoint none) (secondOnePoint (some a)) =
      R.geometry.F none (some a) := by
  cases hattach : R.toPartExtension.attachment with
  | none =>
    exact canonicalOnePointGauge_right_fresh_old D L R hattach a
  | some i =>
    exact canonicalOnePointGauge_right_attached_old
      D L R i hattach a hcross

/-- Every cross-part effective colour from the FIRST original
one-point extension survives the single strong amalgam. -/
theorem effectiveOnePointAmalgam_first_cross
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (x y : Option V)
    (hcross : ¬L.geometry.part x y) :
    (effectiveOnePointAmalgam D L R).F
        (firstOnePoint x) (firstOnePoint y) =
      L.geometry.F x y := by
  let B := effectiveOnePointAmalgam D L R
  cases x with
  | none =>
    cases y with
    | none =>
      exact (hcross (L.geometry.part.iseqv.refl none)).elim
    | some a =>
      exact effectiveOnePointAmalgam_first_new_old D L R a hcross
  | some a =>
    cases y with
    | none =>
      have hback : ¬L.geometry.part none (some a) := by
        intro h
        exact hcross (L.geometry.part.iseqv.symm h)
      have hB : ¬B.part (firstOnePoint none) (firstOnePoint (some a)) := by
        intro hh
        exact hback ((effectiveOnePointAmalgam_first_part
          D L R none (some a)).1 hh)
      have hrevB := B.reverse_cross
        (firstOnePoint none) (firstOnePoint (some a)) hB
      have hrevL := L.geometry.reverse_cross none (some a) hback
      calc
        B.F (firstOnePoint (some a)) (firstOnePoint none) =
          s (B.F (firstOnePoint none) (firstOnePoint (some a))) := hrevB
        _ = s (L.geometry.F none (some a)) := by
          rw [effectiveOnePointAmalgam_first_new_old D L R a hback]
        _ = L.geometry.F (some a) none := hrevL.symm
    | some b =>
      have hab : ¬D.part a b := by
        intro h
        exact hcross ((L.old_part a b).2 h)
      calc
        B.F (firstOnePoint (some a)) (firstOnePoint (some b)) =
          D.F a b := canonicalOnePointGauge_old_old D L R a b hab
        _ = L.geometry.F (some a) (some b) := (L.old_F a b).symm

/-- The symmetric full cross-part preservation statement for
the SECOND original one-point extension. -/
theorem effectiveOnePointAmalgam_second_cross
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (x y : Option V)
    (hcross : ¬R.geometry.part x y) :
    (effectiveOnePointAmalgam D L R).F
        (secondOnePoint x) (secondOnePoint y) =
      R.geometry.F x y := by
  let B := effectiveOnePointAmalgam D L R
  cases x with
  | none =>
    cases y with
    | none =>
      exact (hcross (R.geometry.part.iseqv.refl none)).elim
    | some a =>
      exact effectiveOnePointAmalgam_second_new_old D L R a hcross
  | some a =>
    cases y with
    | none =>
      have hback : ¬R.geometry.part none (some a) := by
        intro h
        exact hcross (R.geometry.part.iseqv.symm h)
      have hB : ¬B.part (secondOnePoint none) (secondOnePoint (some a)) := by
        intro hh
        exact hback ((effectiveOnePointAmalgam_second_part
          D L R none (some a)).1 hh)
      have hrevB := B.reverse_cross
        (secondOnePoint none) (secondOnePoint (some a)) hB
      have hrevR := R.geometry.reverse_cross none (some a) hback
      calc
        B.F (secondOnePoint (some a)) (secondOnePoint none) =
          s (B.F (secondOnePoint none) (secondOnePoint (some a))) := hrevB
        _ = s (R.geometry.F none (some a)) := by
          rw [effectiveOnePointAmalgam_second_new_old D L R a hback]
        _ = R.geometry.F (some a) none := hrevR.symm
    | some b =>
      have hab : ¬D.part a b := by
        intro h
        exact hcross ((R.old_part a b).2 h)
      calc
        B.F (secondOnePoint (some a)) (secondOnePoint (some b)) =
          D.F a b := canonicalOnePointGauge_old_old D L R a b hab
        _ = R.geometry.F (some a) (some b) := (R.old_F a b).symm

/-- Complete effective one-point strong amalgamation: the two new
points remain DISTINCT, the old carrier is identified exactly,
both E-relations are preserved and reflected, and every cross-part
effective colour on either side is preserved literally. -/
theorem effective_onePoint_strong_amalgamation
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D) :
    ∃ B : EffectiveGeometry s (TwoPointCarrier V),
      (∀ x y : Option V,
        B.part (firstOnePoint x) (firstOnePoint y) ↔ L.geometry.part x y) ∧
      (∀ x y : Option V,
        B.part (secondOnePoint x) (secondOnePoint y) ↔ R.geometry.part x y) ∧
      (∀ x y : Option V, ¬L.geometry.part x y →
        B.F (firstOnePoint x) (firstOnePoint y) = L.geometry.F x y) ∧
      (∀ x y : Option V, ¬R.geometry.part x y →
        B.F (secondOnePoint x) (secondOnePoint y) = R.geometry.F x y) := by
  exact ⟨effectiveOnePointAmalgam D L R,
    effectiveOnePointAmalgam_first_part D L R,
    effectiveOnePointAmalgam_second_part D L R,
    effectiveOnePointAmalgam_first_cross D L R,
    effectiveOnePointAmalgam_second_cross D L R⟩

end SemigenericEPPA
