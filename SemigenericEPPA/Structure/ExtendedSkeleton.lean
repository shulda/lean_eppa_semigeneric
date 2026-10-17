import SemigenericEPPA.Structure.IndexedGauge
import SemigenericEPPA.Structure.QuotientGaugeConverse

/-!
# Affine skeleton on old and (possibly unused) fresh part labels

Given the old canonical quotient skeleton, extend it to labels
  (V/E) ⊕ Bool
of a strong one-point amalgam. The two fresh labels may be unoccupied.

For an old label i and fresh label f, use
  K(i,f) = 1,    K(f,i) = s(1).
Between the two fresh labels use the same asymmetric pair. These
choices satisfy K(j,i) = s(K(i,j)), including the nontrivial affine
case s(1) ≠ 1.

This is a *concrete* skeleton choice for the global one-point SAP
gauge algorithm, not yet the vertex-gauge choice or the whole amalgam.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- Extend a quotient-indexed skeleton to old/fresh labels.
No quotient surjectivity assumptions are made. -/
def extendedSkeleton (Q : QuotientGauge s V) :
    (Quotient Q.part ⊕ Bool) → (Quotient Q.part ⊕ Bool) → G
  | Sum.inl i, Sum.inl j => Q.skeleton i j
  | Sum.inl _, Sum.inr _ => 1
  | Sum.inr _, Sum.inl _ => s 1
  | Sum.inr false, Sum.inr true => 1
  | Sum.inr true, Sum.inr false => s 1
  | Sum.inr _, Sum.inr _ => 1

/-- The extended skeleton has EXACT affine reversal, even though
its unused/phantom fresh labels need not represent real vertices. -/
theorem extendedSkeleton_reverse (Q : QuotientGauge s V)
    (i j : Quotient Q.part ⊕ Bool)
    (hij : i ≠ j) :
    extendedSkeleton Q j i = s (extendedSkeleton Q i j) := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hne : i ≠ j := by
        intro h
        apply hij
        simp only [h]
      change Q.skeleton j i = s (Q.skeleton i j)
      exact Q.skeleton_reverse i j hne
    | inr b =>
      cases b <;> rfl
  | inr a =>
    cases j with
    | inl j =>
      change (1 : G) = s (s 1)
      exact (s.involutive 1).symm
    | inr b =>
      cases a <;> cases b
      · exact (hij rfl).elim
      · rfl
      · change (1 : G) = s (s 1)
        exact (s.involutive 1).symm
      · exact (hij rfl).elim

@[simp] theorem extendedSkeleton_old_old
    (Q : QuotientGauge s V) (i j : Quotient Q.part) :
    extendedSkeleton Q (Sum.inl i) (Sum.inl j) = Q.skeleton i j :=
  rfl

@[simp] theorem extendedSkeleton_old_fresh
    (Q : QuotientGauge s V) (i : Quotient Q.part) (b : Bool) :
    extendedSkeleton Q (Sum.inl i) (Sum.inr b) = 1 :=
  rfl

@[simp] theorem extendedSkeleton_fresh_old
    (Q : QuotientGauge s V) (i : Quotient Q.part) (b : Bool) :
    extendedSkeleton Q (Sum.inr b) (Sum.inl i) = s 1 :=
  rfl

@[simp] theorem extendedSkeleton_first_second
    (Q : QuotientGauge s V) :
    extendedSkeleton Q (Sum.inr false) (Sum.inr true) = 1 :=
  rfl

@[simp] theorem extendedSkeleton_second_first
    (Q : QuotientGauge s V) :
    extendedSkeleton Q (Sum.inr true) (Sum.inr false) = s 1 :=
  rfl

/-- A concrete skeleton for the global two-new-vertex amalgam,
with precisely the old colours of D and prescribed fresh constants. -/
noncomputable def onePointSkeleton
    (D : EffectiveGeometry s V) :
    (Quotient D.part ⊕ Bool) → (Quotient D.part ⊕ Bool) → G :=
  extendedSkeleton D.toQuotientGauge

theorem onePointSkeleton_reverse
    (D : EffectiveGeometry s V)
    (i j : Quotient D.part ⊕ Bool) (hij : i ≠ j) :
    onePointSkeleton D j i = s (onePointSkeleton D i j) :=
  extendedSkeleton_reverse D.toQuotientGauge i j hij

/-- Once the vertex gauges λ are selected, the resulting effective
geometry automatically has the exact strong amalgam E-relation. -/
noncomputable def onePointSkeletonGauge
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (λ : TwoPointCarrier V → (Quotient D.part ⊕ Bool) → G) :
    IndexedGauge s (TwoPointCarrier V) (Quotient D.part ⊕ Bool) :=
  onePointIndexedGauge D L R
    (onePointSkeleton D) (onePointSkeleton_reverse D) λ

theorem onePointSkeletonGauge_part
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (λ : TwoPointCarrier V → (Quotient D.part ⊕ Bool) → G)
    (x y : TwoPointCarrier V) :
    (onePointSkeletonGauge D L R λ).toEffectiveGeometry.part x y ↔
      (amalgamPartSetoid D.part L.toPartExtension R.toPartExtension) x y :=
  onePointIndexedGauge_part D L R
    (onePointSkeleton D) (onePointSkeleton_reverse D) λ x y

end SemigenericEPPA
