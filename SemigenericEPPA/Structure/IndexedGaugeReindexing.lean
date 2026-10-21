import SemigenericEPPA.Structure.IndexedGauge
import SemigenericEPPA.Structure.FixedFibreQuotientGroupAction

/-!
# Reindexing effective gauges without changing any E/F geometry

The fixed factorial padding uses an index sort I; the relative
nontrivial-G H-action theorem expects an IndexedGauge whose indices
are literally Quotient B.part. These are equivalent, but not
definitionally equal. Arbitrary identifier substitutions must NOT
change skeleton matrices or gauge coordinates.

For any equivalence e : I ≃ J we transport the part labels along e
and transport every matrix coordinate back along e.symm. The
resulting actual effective geometry has exactly the same E and F,
including the dummy same-E values.

When a fixed equal-fibre geometry B has E precisely equality of
the first-coordinate index, the previously certified explicit
Quotient B.part ≃ I can be used to turn its given IndexedGauge
Q indexed by I into one indexed by the REAL Quotient B.part.

The reindexing is canonical from the chosen equivalence and is
independent of all later selected induced subsets and H-actions.
It does not assume commutativity of G or s(1)=1.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {V : Type v} {I : Type w} {J : Type t}
variable {s : AffineAntiInvolution G}

namespace IndexedGauge

/-- Transport an actual gauge along an index equivalence.
Crucially the resulting skeleton and old incidence matrix are
conjugated by the SAME equivalence. -/
def reindexedPartLabels
    (P : IndexedGauge s V I)
    (e : I ≃ J) : IndexedGauge s V J where
  label := fun x => e (P.label x)
  skeleton := fun i j => P.skeleton (e.symm i) (e.symm j)
  skeleton_reverse := by
    intro i j hij
    have hne : e.symm i ≠ e.symm j := by
      intro heq
      exact hij (e.symm.injective heq)
    exact P.skeleton_reverse (e.symm i) (e.symm j) hne
  vertexGauge := fun x j => P.vertexGauge x (e.symm j)

/-- Reindexing preserves AND reflects literal E class membership. -/
theorem reindexedPartLabels_part
    (P : IndexedGauge s V I)
    (e : I ≃ J) (x y : V) :
    (P.reindexedPartLabels e).toEffectiveGeometry.part x y ↔
      P.toEffectiveGeometry.part x y := by
  change (e (P.label x) = e (P.label y)) ↔
    P.label x = P.label y
  constructor
  · intro heq
    exact e.injective heq
  · intro heq
    exact congrArg e heq

/-- Every group-valued effective colour is preserved, not merely
its affine congruence class. Same-part dummy values are also 1. -/
theorem reindexedPartLabels_effective
    (P : IndexedGauge s V I)
    (e : I ≃ J) (x y : V) :
    (P.reindexedPartLabels e).effective x y = P.effective x y := by
  classical
  by_cases hxy : P.label x = P.label y
  · have hxy' : (P.reindexedPartLabels e).label x =
        (P.reindexedPartLabels e).label y :=
      congrArg e hxy
    simp [IndexedGauge.effective, hxy, hxy']
  · have hxy' : (P.reindexedPartLabels e).label x ≠
        (P.reindexedPartLabels e).label y := by
      intro heq
      exact hxy (e.injective heq)
    rw [(P.reindexedPartLabels e).effective_cross x y hxy',
      P.effective_cross x y hxy]
    simp [reindexedPartLabels]

/-- A globally constant skeleton remains the SAME constant,
including on all previously unused indices. -/
theorem reindexedPartLabels_constant_skeleton
    (P : IndexedGauge s V I)
    (e : I ≃ J)
    (g0 : G)
    (hConst : ∀ i j : I, P.skeleton i j = g0)
    (i j : J) :
    (P.reindexedPartLabels e).skeleton i j = g0 :=
  hConst (e.symm i) (e.symm j)

/-- Normalized old self-coordinates survive index reparametrization
literally, without comparing different Fintype enumerations. -/
theorem reindexedPartLabels_diagonal
    (P : IndexedGauge s V I)
    (e : I ≃ J)
    (x : V) :
    (P.reindexedPartLabels e).vertexGauge x
      ((P.reindexedPartLabels e).label x) =
        P.vertexGauge x (P.label x) := by
  change P.vertexGauge x (e.symm (e (P.label x))) =
    P.vertexGauge x (P.label x)
  rw [e.symm_apply_apply]

end IndexedGauge

/-- With a nonempty fixed fibre, an indexed gauge on I × Fin M
whose class label is fst can be represented *literally* on the
actual quotient of its own E relation. It preserves all effective
colours and any constant-skeleton / diagonal normalization data.

The output is exactly the API expected by the fixed-witness
nontrivial-G relative effective H-lift theorem. -/
theorem exists_fixedFibreGauge_onActualQuotient
    (M : ℕ) (hpos : 0 < M)
    (Q : IndexedGauge s (I × Fin M) I)
    (hLabel : ∀ w : I × Fin M, Q.label w = w.1)
    (g0 : G) (hConst : ∀ i j : I, Q.skeleton i j = g0) :
    ∃ P : IndexedGauge s (I × Fin M)
          (Quotient Q.toEffectiveGeometry.part),
      (∀ w : I × Fin M,
        P.label w = Quotient.mk Q.toEffectiveGeometry.part w) ∧
      (∀ i j : Quotient Q.toEffectiveGeometry.part,
        P.skeleton i j = g0) ∧
      (∀ w : I × Fin M,
        P.vertexGauge w (P.label w) =
          Q.vertexGauge w (Q.label w)) ∧
      (∀ x y : I × Fin M,
        P.toEffectiveGeometry.part x y ↔
          Q.toEffectiveGeometry.part x y) ∧
      (∀ x y : I × Fin M,
        P.toEffectiveGeometry.F x y =
          Q.toEffectiveGeometry.F x y) := by
  let B : EffectiveGeometry s (I × Fin M) :=
    Q.toEffectiveGeometry
  have hB : ∀ z w : I × Fin M,
      B.part z w ↔ z.1 = w.1 := by
    intro z w
    change Q.label z = Q.label w ↔ z.1 = w.1
    rw [hLabel z, hLabel w]
  let e : Quotient B.part ≃ I :=
    fixedFibreQuotientEquiv M hpos B hB
  let P : IndexedGauge s (I × Fin M) (Quotient B.part) :=
    Q.reindexedPartLabels e.symm
  have hPlabel (w : I × Fin M) :
      P.label w = Quotient.mk B.part w := by
    apply e.injective
    change e (e.symm (Q.label w)) =
      e (Quotient.mk B.part w)
    rw [e.apply_symm_apply, hLabel w]
    rfl
  refine ⟨P, hPlabel, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact Q.reindexedPartLabels_constant_skeleton
      e.symm g0 hConst i j
  · intro w
    exact Q.reindexedPartLabels_diagonal e.symm w
  · intro x y
    exact Q.reindexedPartLabels_part e.symm x y
  · intro x y
    exact Q.reindexedPartLabels_effective e.symm x y

end SemigenericEPPA
