import SemigenericEPPA.Structure.OnePointGaugeChoice
import SemigenericEPPA.Structure.AttachedGaugeFactor

/-!
# The global labelled gauge preserves attached-new/old cross colours

This is the principal nontrivial side-preservation calculation for
global effective one-point strong amalgamation. Suppose one of the
new vertices is attached to an old E-class i. The global label gauge
selects the old representative p of i and old q of the class of a.
For every old a OUTSIDE the attached E-class, the label-gauge formula
reconstructs the original one-point colour F(new,a) exactly.

The proof invokes the genuine R3 side formula from
AttachedGaugeFactor, not a new algebraic assumption. Both new
vertices are handled independently and symmetrically.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- The first new vertex, attached to an old E-class, retains
all its prescribed cross-part effective colours toward old points. -/
theorem canonicalOnePointGauge_left_attached_old
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (i : Quotient D.part)
    (hattach : L.toPartExtension.attachment = some i)
    (a : V) (hcross : ¬L.geometry.part none (some a)) :
    (canonicalOnePointGauge D L R).toEffectiveGeometry.F
      (Sum.inr false) (Sum.inl a) =
        L.geometry.F none (some a) := by
  let P := canonicalOnePointGauge D L R
  let p := D.representative i
  let q := D.representative (Quotient.mk D.part a)
  have hrep : Quotient.mk D.part p = i := Quotient.out_eq i
  have hnewp : L.geometry.part none (some p) := by
    have happ : L.toPartExtension.attachment =
        some (Quotient.mk D.part p) := by
      rw [hrep]
      exact hattach
    exact (L.toPartExtension.rel_none_some_iff_attachment p).2 happ
  have hqa : D.part q a :=
    D.part.iseqv.symm (D.related_representative a)
  have hpq : ¬D.part p q := by
    intro hpq
    have hnewq : L.geometry.part none (some q) :=
      L.geometry.part.iseqv.trans hnewp ((L.old_part p q).2 hpq)
    have hnewa : L.geometry.part none (some a) :=
      L.geometry.part.iseqv.trans hnewq ((L.old_part q a).2 hqa)
    exact hcross hnewa
  have hindex : i ≠ Quotient.mk D.part a := by
    intro hia
    have hpa : D.part p a :=
      Quotient.exact (hrep.trans hia)
    exact hcross
      (L.geometry.part.iseqv.trans hnewp ((L.old_part p a).2 hpa))
  have hlabel : P.label (Sum.inr false) ≠ P.label (Sum.inl a) := by
    have hn : P.label (Sum.inr false) = Sum.inl i := by
      simp [P, canonicalOnePointGauge, onePointSkeletonGauge,
        onePointIndexedGauge, combinedPartIndex,
        OnePointPartExtension.index, hattach]
    have ha : P.label (Sum.inl a) =
        Sum.inl (Quotient.mk D.part a) := rfl
    rw [hn, ha]
    intro h
    exact hindex (Sum.inl.inj h)
  have hg := P.effective_cross (Sum.inr false) (Sum.inl a) hlabel
  have hformula :
      P.toEffectiveGeometry.F (Sum.inr false) (Sum.inl a) =
      gaugeColour s (L.geometry.F (some q) none)
        (D.F p q) (D.F p a) := by
    calc
      P.toEffectiveGeometry.F (Sum.inr false) (Sum.inl a) =
          P.effective (Sum.inr false) (Sum.inl a) := rfl
      _ = gaugeColour s (L.geometry.F (some q) none)
            (D.F p q) (D.F p a) := by
          simpa [P, canonicalOnePointGauge, onePointSkeletonGauge,
            onePointIndexedGauge, combinedPartIndex,
            OnePointPartExtension.index, onePointSkeleton,
            extendedSkeleton, onePointVertexGauge,
            hattach] using hg
  calc
    P.toEffectiveGeometry.F (Sum.inr false) (Sum.inl a) =
      gaugeColour s (L.geometry.F (some q) none)
        (D.F p q) (D.F p a) := hformula
    _ = L.geometry.F none (some a) := by
      change s (L.geometry.F (some q) none) *
        (D.F p q)⁻¹ * D.F p a = L.geometry.F none (some a)
      exact (onePoint_attached_new_to_old_formula
        D L p q a hnewp hqa hpq).symm

/-- The symmetric assertion for the second one-point extension. -/
theorem canonicalOnePointGauge_right_attached_old
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (i : Quotient D.part)
    (hattach : R.toPartExtension.attachment = some i)
    (a : V) (hcross : ¬R.geometry.part none (some a)) :
    (canonicalOnePointGauge D L R).toEffectiveGeometry.F
      (Sum.inr true) (Sum.inl a) =
        R.geometry.F none (some a) := by
  let P := canonicalOnePointGauge D L R
  let p := D.representative i
  let q := D.representative (Quotient.mk D.part a)
  have hrep : Quotient.mk D.part p = i := Quotient.out_eq i
  have hnewp : R.geometry.part none (some p) := by
    have happ : R.toPartExtension.attachment =
        some (Quotient.mk D.part p) := by
      rw [hrep]
      exact hattach
    exact (R.toPartExtension.rel_none_some_iff_attachment p).2 happ
  have hqa : D.part q a :=
    D.part.iseqv.symm (D.related_representative a)
  have hpq : ¬D.part p q := by
    intro hpq
    have hnewq : R.geometry.part none (some q) :=
      R.geometry.part.iseqv.trans hnewp ((R.old_part p q).2 hpq)
    have hnewa : R.geometry.part none (some a) :=
      R.geometry.part.iseqv.trans hnewq ((R.old_part q a).2 hqa)
    exact hcross hnewa
  have hindex : i ≠ Quotient.mk D.part a := by
    intro hia
    have hpa : D.part p a :=
      Quotient.exact (hrep.trans hia)
    exact hcross
      (R.geometry.part.iseqv.trans hnewp ((R.old_part p a).2 hpa))
  have hlabel : P.label (Sum.inr true) ≠ P.label (Sum.inl a) := by
    have hn : P.label (Sum.inr true) = Sum.inl i := by
      simp [P, canonicalOnePointGauge, onePointSkeletonGauge,
        onePointIndexedGauge, combinedPartIndex,
        OnePointPartExtension.index, hattach]
    have ha : P.label (Sum.inl a) =
        Sum.inl (Quotient.mk D.part a) := rfl
    rw [hn, ha]
    intro h
    exact hindex (Sum.inl.inj h)
  have hg := P.effective_cross (Sum.inr true) (Sum.inl a) hlabel
  have hformula :
      P.toEffectiveGeometry.F (Sum.inr true) (Sum.inl a) =
      gaugeColour s (R.geometry.F (some q) none)
        (D.F p q) (D.F p a) := by
    calc
      P.toEffectiveGeometry.F (Sum.inr true) (Sum.inl a) =
          P.effective (Sum.inr true) (Sum.inl a) := rfl
      _ = gaugeColour s (R.geometry.F (some q) none)
            (D.F p q) (D.F p a) := by
          simpa [P, canonicalOnePointGauge, onePointSkeletonGauge,
            onePointIndexedGauge, combinedPartIndex,
            OnePointPartExtension.index, onePointSkeleton,
            extendedSkeleton, onePointVertexGauge,
            hattach] using hg
  calc
    P.toEffectiveGeometry.F (Sum.inr true) (Sum.inl a) =
      gaugeColour s (R.geometry.F (some q) none)
        (D.F p q) (D.F p a) := hformula
    _ = R.geometry.F none (some a) := by
      change s (R.geometry.F (some q) none) *
        (D.F p q)⁻¹ * D.F p a = R.geometry.F none (some a)
      exact (onePoint_attached_new_to_old_formula
        D R p q a hnewp hqa hpq).symm

end SemigenericEPPA
