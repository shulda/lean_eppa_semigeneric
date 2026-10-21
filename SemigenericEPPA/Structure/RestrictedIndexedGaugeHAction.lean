import SemigenericEPPA.Structure.IndexedGauge
import Mathlib.Algebra.Group.End

/-!
# The indexed gauge on a genuinely H-invariant old selected subset

For coherent EPPA of a finite structure A, a finite H acts on a
selected induced substructure S, not necessarily on the WHOLE ambient
old geometry. The occupied multipliers must therefore be built from
the actual E/F matrix on S, with no false preservation assumptions on
colours incident with A\\S.

An arbitrary indexed gauge P on V restricts literally to a gauge
presentation on the subtype S. An actual H-action on V preserving the
set S restricts to a strict homomorphism H -> Perm S. Under E-index
compatibility and effective F-invariance ONLY FOR PAIRS IN S, the
restricted action satisfies the precise hypotheses of the occupied
gauge multiplier algebra.

There is no finiteness, commutativity, affine normalization, or
unnecessary global colour-preservation assumption.
-/

namespace SemigenericEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {V : Type w} {I : Type t}
variable {s : AffineAntiInvolution G}

namespace IndexedGauge

/-- Restriction to the true induced subset, preserving the SAME
imaginary part-index type even if some indices become unused. -/
def restrictSubset (P : IndexedGauge s V I) (S : Set V) :
    IndexedGauge s S I where
  label := fun x => P.label x.val
  skeleton := P.skeleton
  skeleton_reverse := P.skeleton_reverse
  vertexGauge := fun x j => P.vertexGauge x.val j

/-- The restricted gauge has exactly the original E-classes. -/
theorem restrictSubset_part
    (P : IndexedGauge s V I) (S : Set V)
    (x y : S) :
    (P.restrictSubset S).toEffectiveGeometry.part x y ↔
      P.toEffectiveGeometry.part x.val y.val := Iff.rfl

/-- The restriction preserves literal effective F-values even for
the dummy values on pairs inside one E-class. -/
theorem restrictSubset_effective
    (P : IndexedGauge s V I) (S : Set V)
    (x y : S) :
    (P.restrictSubset S).toEffectiveGeometry.F x y =
      P.toEffectiveGeometry.F x.val y.val := rfl

end IndexedGauge

/-- The restriction to an H-invariant subset S of a real old-label
permutation. A genuine Equiv is returned, not just a partial map. -/
def selectedSubsetPerm
    (S : Set V) (rho : H →* Equiv.Perm V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (h : H) : Equiv.Perm S where
  toFun := fun x => ⟨rho h x.val, (hS h x.val).mp x.property⟩
  invFun := fun x => ⟨(rho h).symm x.val, by
    apply (hS h ((rho h).symm x.val)).mpr
    simpa only [(rho h).apply_symm_apply] using x.property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact (rho h).symm_apply_apply x.val
  right_inv := by
    intro x
    apply Subtype.ext
    exact (rho h).apply_symm_apply x.val

/-- One strict H-action on the ACTUAL subset S. The same homomorphism
laws hold, rather than independently extending each old permutation. -/
def selectedSubsetAction
    (S : Set V) (rho : H →* Equiv.Perm V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S) :
    H →* Equiv.Perm S where
  toFun := selectedSubsetPerm S rho hS
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change rho (1 : H) x.val = x.val
    simp
  map_mul' := by
    intro k h
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change rho (k * h) x.val = rho k (rho h x.val)
    rw [map_mul]
    rfl

@[simp] theorem selectedSubsetAction_val
    (S : Set V) (rho : H →* Equiv.Perm V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (h : H) (x : S) :
    (selectedSubsetAction S rho hS h x).val = rho h x.val := rfl

/-- All matrix-invariance and index-action hypotheses needed by the
canonical occupied-gauge multiplier construction are inherited from
genuine H-automorphisms of S only. No F-invariance outside S. -/
theorem IndexedGauge.restrictSubset_H_data
    (P : IndexedGauge s V I) (S : Set V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (hLabel : ∀ (h : H) (x : S),
      P.label (rho h x.val) = iota h (P.label x.val))
    (hF : ∀ (h : H) (x y : S),
      P.label x.val ≠ P.label y.val →
      P.toEffectiveGeometry.F (rho h x.val) (rho h y.val) =
        P.toEffectiveGeometry.F x.val y.val) :
    (∀ (h : H) (x : S),
      (P.restrictSubset S).label
        (selectedSubsetAction S rho hS h x) =
        iota h ((P.restrictSubset S).label x)) ∧
    (∀ (h : H) (x y : S),
      ¬(P.restrictSubset S).toEffectiveGeometry.part x y →
      (P.restrictSubset S).toEffectiveGeometry.F
        (selectedSubsetAction S rho hS h x)
        (selectedSubsetAction S rho hS h y) =
      (P.restrictSubset S).toEffectiveGeometry.F x y) := by
  constructor
  · intro h x
    exact hLabel h x
  · intro h x y hxy
    have hne : P.label x.val ≠ P.label y.val := hxy
    change P.toEffectiveGeometry.F (rho h x.val) (rho h y.val) =
      P.toEffectiveGeometry.F x.val y.val
    exact hF h x y hne

end SemigenericEPPA
