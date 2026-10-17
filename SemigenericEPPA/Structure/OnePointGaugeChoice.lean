import SemigenericEPPA.Structure.ExtendedSkeleton

/-!
# Explicit vertex gauges on the global two-new-point carrier

This implements the vertex-coordinate part of the intended global
one-point SAP gauge construction, complementing ExtendedSkeleton.

For old part label j, the old vertex a has coordinate F(rep(j),a).
For a newly attached vertex, use the corresponding one-point
coordinate F_side(rep(j),new). For a new *fresh* vertex, use 1
toward old labels and record its prescribed outgoing edges in the
old vertices' coordinates toward its fresh label.

The formulas involve only the old D and the two one-point extensions,
not an unproved choice of compatible effective geometry. This module
starts the proof that the resulting global geometry restricts to both
one-point extensions exactly.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- Explicit vertex coordinates on the strong two-new-point carrier.
The two fresh labels may be phantom (unoccupied); this causes no problem. -/
noncomputable def onePointVertexGauge
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D) :
    TwoPointCarrier V → (Quotient D.part ⊕ Bool) → G := by
  classical
  exact fun x j => match x, j with
    | Sum.inl a, Sum.inl k => D.F (D.representative k) a
    | Sum.inl a, Sum.inr false => L.geometry.F none (some a)
    | Sum.inl a, Sum.inr true => R.geometry.F none (some a)
    | Sum.inr false, Sum.inl k =>
        if L.toPartExtension.attachment = none then 1
        else L.geometry.F (some (D.representative k)) none
    | Sum.inr true, Sum.inl k =>
        if R.toPartExtension.attachment = none then 1
        else R.geometry.F (some (D.representative k)) none
    | Sum.inr _, Sum.inr _ => 1

/-- A single explicit indexed-gauge datum for the strong amalgam:
the verified canonical class labels, canonical affine skeleton, and
the vertex coordinates above. -/
noncomputable def canonicalOnePointGauge
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D) :
    IndexedGauge s (TwoPointCarrier V) (Quotient D.part ⊕ Bool) :=
  onePointSkeletonGauge D L R (onePointVertexGauge D L R)

/-- The resulting candidate E is the exact strong one-point
equivalence amalgam; no vertices and no old classes are identified. -/
theorem canonicalOnePointGauge_part
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (x y : TwoPointCarrier V) :
    (canonicalOnePointGauge D L R).toEffectiveGeometry.part x y ↔
      (amalgamPartSetoid D.part L.toPartExtension R.toPartExtension) x y :=
  onePointSkeletonGauge_part D L R (onePointVertexGauge D L R) x y

/-- For every cross-part pair of OLD vertices, the explicit global
gauge reconstructs the original effective colour exactly. -/
theorem canonicalOnePointGauge_old_old
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (a b : V) (hab : ¬D.part a b) :
    (canonicalOnePointGauge D L R).toEffectiveGeometry.F
      (Sum.inl a) (Sum.inl b) = D.F a b := by
  let P := canonicalOnePointGauge D L R
  let p := D.representative (Quotient.mk D.part a)
  let q := D.representative (Quotient.mk D.part b)
  have hxp : D.part a p := D.related_representative a
  have hqy : D.part q b :=
    D.part.iseqv.symm (D.related_representative b)
  have hxq : ¬D.part a q := by
    intro h
    exact hab (D.part.iseqv.trans h hqy)
  have hfactor := D.anchored_factor a p q b hxp hqy hxq
  have hreverse : s (D.F q a) = D.F a q := by
    rw [D.reverse_cross a q hxq, s.involutive]
  have hlabel : P.label (Sum.inl a) ≠ P.label (Sum.inl b) := by
    change (Sum.inl (Quotient.mk D.part a) : Quotient D.part ⊕ Bool) ≠
      Sum.inl (Quotient.mk D.part b)
    intro h
    exact hab (Quotient.exact (Sum.inl.inj h))
  have hg := P.effective_cross (Sum.inl a) (Sum.inl b) hlabel
  have hformula :
      P.toEffectiveGeometry.F (Sum.inl a) (Sum.inl b) =
        gaugeColour s (D.F q a) (D.F p q) (D.F p b) := by
    change P.toEffectiveGeometry.F (Sum.inl a) (Sum.inl b) =
      gaugeColour s (D.F q a) (D.F p q) (D.F p b) at hg
    exact hg
  calc
    P.toEffectiveGeometry.F (Sum.inl a) (Sum.inl b) =
      gaugeColour s (D.F q a) (D.F p q) (D.F p b) := hformula
    _ = D.F a q * (D.F p q)⁻¹ * D.F p b := by
      simp only [gaugeColour, hreverse]
    _ = D.F a b := hfactor.symm

/-- If the left new vertex starts its own fresh E-class, its
effective colours toward every old vertex are preserved exactly. -/
theorem canonicalOnePointGauge_left_fresh_old
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (hfresh : L.toPartExtension.attachment = none)
    (a : V) :
    (canonicalOnePointGauge D L R).toEffectiveGeometry.F
      (Sum.inr false) (Sum.inl a) =
        L.geometry.F none (some a) := by
  let P := canonicalOnePointGauge D L R
  have hlabel : P.label (Sum.inr false) ≠ P.label (Sum.inl a) := by
    simp [P, canonicalOnePointGauge, onePointSkeletonGauge,
      onePointIndexedGauge, combinedPartIndex,
      OnePointPartExtension.index, hfresh]
  have hg := P.effective_cross (Sum.inr false) (Sum.inl a) hlabel
  have hformula :
      P.toEffectiveGeometry.F (Sum.inr false) (Sum.inl a) =
      gaugeColour s (1 : G) (s 1) (L.geometry.F none (some a)) := by
    simpa [P, canonicalOnePointGauge, onePointSkeletonGauge,
      onePointIndexedGauge, combinedPartIndex, OnePointPartExtension.index,
      onePointSkeleton, extendedSkeleton, onePointVertexGauge,
      hfresh] using hg
  calc
    P.toEffectiveGeometry.F (Sum.inr false) (Sum.inl a) =
        gaugeColour s (1 : G) (s 1) (L.geometry.F none (some a)) :=
      hformula
    _ = L.geometry.F none (some a) := by
      unfold gaugeColour
      group

/-- The analogous fresh-vertex preservation for the right side. -/
theorem canonicalOnePointGauge_right_fresh_old
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (hfresh : R.toPartExtension.attachment = none)
    (a : V) :
    (canonicalOnePointGauge D L R).toEffectiveGeometry.F
      (Sum.inr true) (Sum.inl a) =
        R.geometry.F none (some a) := by
  let P := canonicalOnePointGauge D L R
  have hlabel : P.label (Sum.inr true) ≠ P.label (Sum.inl a) := by
    simp [P, canonicalOnePointGauge, onePointSkeletonGauge,
      onePointIndexedGauge, combinedPartIndex,
      OnePointPartExtension.index, hfresh]
  have hg := P.effective_cross (Sum.inr true) (Sum.inl a) hlabel
  have hformula :
      P.toEffectiveGeometry.F (Sum.inr true) (Sum.inl a) =
      gaugeColour s (1 : G) (s 1) (R.geometry.F none (some a)) := by
    simpa [P, canonicalOnePointGauge, onePointSkeletonGauge,
      onePointIndexedGauge, combinedPartIndex, OnePointPartExtension.index,
      onePointSkeleton, extendedSkeleton, onePointVertexGauge,
      hfresh] using hg
  calc
    P.toEffectiveGeometry.F (Sum.inr true) (Sum.inl a) =
        gaugeColour s (1 : G) (s 1) (R.geometry.F none (some a)) :=
      hformula
    _ = R.geometry.F none (some a) := by
      unfold gaugeColour
      group

end SemigenericEPPA
