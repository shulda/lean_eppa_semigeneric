import SemigenericEPPA.Structure.QuotientGauge
import SemigenericEPPA.Structure.OnePointEffective

/-!
# Effective gauges indexed by arbitrary part labels

The canonical two-sorted gauge theorem uses labels of type Quotient E.
For the strong one-point amalgam the natural labels instead live in
(Quotient E) ⊕ Bool. This label type includes *unused* fresh labels
when one or both new vertices are attached to existing parts.

This module proves that gauge data work for ANY label type and map
label : V → I, with no surjectivity condition. Equality of labels is
the induced E-equivalence. The exact same noncommutative/affine gauge
formula produces a genuine effective rectangle geometry.

This removes the class-index mismatch in the global SAP assembly plan,
while making no claim yet about selecting compatible gauge data.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {V : Type v} {I : Type w}
variable {s : AffineAntiInvolution G}

/-- Gauges with arbitrary labels of E-parts, including labels that
are not represented by any real vertex. -/
structure IndexedGauge (s : AffineAntiInvolution G) (V : Type v)
    (I : Type w) where
  label : V → I
  skeleton : I → I → G
  skeleton_reverse :
    ∀ i j : I, i ≠ j → skeleton j i = s (skeleton i j)
  vertexGauge : V → I → G

namespace IndexedGauge

variable (P : IndexedGauge s V I)

/-- E is the kernel of the label map. No surjectivity is needed. -/
def part : Setoid V where
  r x y := P.label x = P.label y
  iseqv := by
    constructor
    · intro x
      rfl
    · intro x y hxy
      exact hxy.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz

@[simp] theorem part_iff (x y : V) :
    P.part x y ↔ P.label x = P.label y :=
  Iff.rfl

/-- An arbitrary value on same-part pairs is irrelevant.
The value 1 is a convenient representative, not a fixed point of s. -/
noncomputable def effective (x y : V) : G := by
  classical
  exact if P.label x = P.label y then 1
    else gaugeColour s
      (P.vertexGauge x (P.label y))
      (P.skeleton (P.label x) (P.label y))
      (P.vertexGauge y (P.label x))

theorem effective_cross (x y : V)
    (hxy : P.label x ≠ P.label y) :
    P.effective x y =
      gaugeColour s
        (P.vertexGauge x (P.label y))
        (P.skeleton (P.label x) (P.label y))
        (P.vertexGauge y (P.label x)) := by
  simp [effective, hxy]

theorem effective_reverse (x y : V)
    (hxy : P.label x ≠ P.label y) :
    P.effective y x = s (P.effective x y) := by
  have hyx : P.label y ≠ P.label x := Ne.symm hxy
  rw [P.effective_cross y x hyx, P.effective_cross x y hxy]
  rw [P.skeleton_reverse (P.label x) (P.label y) hxy]
  exact (gauge_reverse s
    (P.vertexGauge x (P.label y))
    (P.skeleton (P.label x) (P.label y))
    (P.vertexGauge y (P.label x))).symm

/-- The complete rectangle equation holds on every pair of distinct
labels; it does not require that any given label be inhabited. -/
theorem effective_rectangle
    (x₀ x₁ y₀ y₁ : V)
    (hx : P.label x₀ = P.label x₁)
    (hy : P.label y₀ = P.label y₁)
    (h00 : P.label x₀ ≠ P.label y₀) :
    (P.effective x₀ y₀)⁻¹ * P.effective x₀ y₁ =
      (P.effective x₁ y₀)⁻¹ * P.effective x₁ y₁ := by
  have h01 : P.label x₀ ≠ P.label y₁ := by
    intro h
    exact h00 (h.trans hy.symm)
  have h10 : P.label x₁ ≠ P.label y₀ := by
    intro h
    exact h00 (hx.trans h)
  have h11 : P.label x₁ ≠ P.label y₁ := by
    intro h
    exact h00 (hx.trans (h.trans hy.symm))
  have hr := gauge_rectangle s
    (P.skeleton (P.label x₀) (P.label y₀))
    (fun x => P.vertexGauge x (P.label y₀))
    (fun y => P.vertexGauge y (P.label x₀))
    x₀ x₁ y₀ y₁
  rw [P.effective_cross x₀ y₀ h00,
    P.effective_cross x₀ y₁ h01,
    P.effective_cross x₁ y₀ h10,
    P.effective_cross x₁ y₁ h11]
  have hx' : P.label x₁ = P.label x₀ := hx.symm
  have hy' : P.label y₁ = P.label y₀ := hy.symm
  simp only [hx', hy']
  exact hr

/-- Every indexed gauge produces a genuine effective E-rectangle
geometry, without any hypothesis about surjectivity of labels. -/
noncomputable def toEffectiveGeometry : EffectiveGeometry s V where
  part := P.part
  F := P.effective
  reverse_cross := by
    intro x y hxy
    exact P.effective_reverse x y hxy
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy h00
    exact P.effective_rectangle x₀ x₁ y₀ y₁ hx hy h00

theorem toEffectiveGeometry_part (x y : V) :
    P.toEffectiveGeometry.part x y ↔ P.label x = P.label y :=
  Iff.rfl

/-- The canonical quotient-sorted construction is a special case
of the arbitrary-label construction. -/
def ofQuotientGauge (Q : QuotientGauge s V) :
    IndexedGauge s V (Quotient Q.part) where
  label := Q.cls
  skeleton := Q.skeleton
  skeleton_reverse := Q.skeleton_reverse
  vertexGauge := Q.vertexGauge

theorem ofQuotientGauge_effective (Q : QuotientGauge s V)
    (x y : V) :
    (ofQuotientGauge Q).effective x y = Q.effective x y := by
  classical
  by_cases hpart : Q.part x y
  · have hlabel : Q.cls x = Q.cls y :=
      (Q.cls_eq_iff x y).2 hpart
    simp [IndexedGauge.effective, ofQuotientGauge,
      QuotientGauge.effective, hlabel, hpart]
  · have hlabel : Q.cls x ≠ Q.cls y := by
      intro heq
      exact hpart ((Q.cls_eq_iff x y).1 heq)
    rw [IndexedGauge.effective_cross (ofQuotientGauge Q) x y hlabel,
      Q.effective_cross x y hpart]
    rfl

end IndexedGauge

/-- On a strong two-new-vertex carrier, the canonical class-index
function is an appropriate label map, regardless of unoccupied labels.
The skeleton and gauge coordinates will be chosen by the SAP proof. -/
def onePointIndexedGauge
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (K : (Quotient D.part ⊕ Bool) →
         (Quotient D.part ⊕ Bool) → G)
    (hK : ∀ i j : Quotient D.part ⊕ Bool,
      i ≠ j → K j i = s (K i j))
    (coords : TwoPointCarrier V → (Quotient D.part ⊕ Bool) → G) :
    IndexedGauge s (TwoPointCarrier V) (Quotient D.part ⊕ Bool) where
  label := combinedPartIndex D.part
    L.toPartExtension R.toPartExtension
  skeleton := K
  skeleton_reverse := hK
  vertexGauge := coords

/-- The E-partition reconstructed from such arbitrary-label gauges
is exactly the previously verified strong one-point part amalgam. -/
theorem onePointIndexedGauge_part
    (D : EffectiveGeometry s V)
    (L R : OnePointEffectiveExtension D)
    (K : (Quotient D.part ⊕ Bool) →
         (Quotient D.part ⊕ Bool) → G)
    (hK : ∀ i j : Quotient D.part ⊕ Bool,
      i ≠ j → K j i = s (K i j))
    (coords : TwoPointCarrier V → (Quotient D.part ⊕ Bool) → G)
    (x y : TwoPointCarrier V) :
    (onePointIndexedGauge D L R K hK coords).toEffectiveGeometry.part x y ↔
      (amalgamPartSetoid D.part L.toPartExtension R.toPartExtension) x y :=
  Iff.rfl

end SemigenericEPPA
