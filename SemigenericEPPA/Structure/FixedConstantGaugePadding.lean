import SemigenericEPPA.Structure.IndexedGauge
import Mathlib.Data.Fintype.Prod

/-!
# Prechosen equal-fibre padding with one constant affine skeleton

Fix an old indexed gauge P on A with E-class index sort I, any
finite-fibre size M and ONE injective original coding j:A→Fin M.

The padded auxiliary old-label carrier W=I×Fin M is selected before
any induced subset S or finite automorphism group H. The original
vertex x has the unchangeable embedding
  old(x)=(P.label x,j(x)).

Given a single s-fixed skeleton value g0, construct a genuine indexed
gauge Q on W with constant skeleton g0 and E given by equality of
the I-coordinates. At all padded labels, the same-part (diagonal)
gauge coordinate is set to 1. At the old labels, cross-part
coordinates agree with those of P; every other unused coordinate
is chosen to be 1.

When P already has the same constant skeleton g0, Q contains the old
effective E/F geometry inducedly and literally. Crucially the
choice of Q is independent of S, H and every later group action.
It is therefore suitable as the fixed base of the simultaneous
nontrivial-G coherent positive construction.

All identities work without recentering, commutativity, or s(1)=1.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {A : Type v} {I : Type w}
variable {s : AffineAntiInvolution G}

namespace IndexedGauge

/-- Original old vertices inside one globally prechosen product
carrier, using ONE fixed injection shared by all E-parts. -/
def fixedUniformPaddingOldMap
    (P : IndexedGauge s A I) {M : ℕ}
    (j : A → Fin M) (x : A) : I × Fin M :=
  (P.label x, j x)

/-- The fixed old embedding is injective even when several old
vertices have the same E-class index. -/
theorem fixedUniformPaddingOldMap_injective
    (P : IndexedGauge s A I) {M : ℕ}
    (j : A → Fin M) (hj : Function.Injective j) :
    Function.Injective (P.fixedUniformPaddingOldMap j) := by
  intro x y heq
  exact hj (congrArg Prod.snd heq)

/-- An old gauge row at an embedded padded label is remembered
literally, but only on CROSS-class target indices. Diagonal
coordinates are normalized to 1 and all other new labels use 1. -/
noncomputable def fixedUniformPaddingRow
    (P : IndexedGauge s A I) {M : ℕ}
    (j : A → Fin M)
    (w : I × Fin M) (k : I) : G := by
  classical
  exact if hk : k = w.1 then 1
    else if hw : ∃ x : A, P.fixedUniformPaddingOldMap j x = w then
      P.vertexGauge (Classical.choose hw) k
    else 1

/-- On the original labelled copy, every cross-class gauge row
agrees EXACTLY with its prescribed old value. The witness picked
by Classical.choose equals x by injectivity of the fixed map. -/
theorem fixedUniformPaddingRow_old
    (P : IndexedGauge s A I) {M : ℕ}
    (j : A → Fin M) (hj : Function.Injective j)
    (x : A) (k : I) (hcross : P.label x ≠ k) :
    P.fixedUniformPaddingRow j (P.fixedUniformPaddingOldMap j x) k =
      P.vertexGauge x k := by
  classical
  have hk : k ≠ (P.fixedUniformPaddingOldMap j x).1 :=
    hcross.symm
  have hw : ∃ y : A,
      P.fixedUniformPaddingOldMap j y =
        P.fixedUniformPaddingOldMap j x := ⟨x, rfl⟩
  have hchoose : Classical.choose hw = x :=
    P.fixedUniformPaddingOldMap_injective j hj
      (Classical.choose_spec hw)
  simp [fixedUniformPaddingRow, hk, hw, hchoose]

/-- The entire fixed padding has one constant s-fixed skeleton.
Unlike a naive extension of old labels, this is an actual
IndexedGauge and therefore automatically obeys R3 rectangles. -/
noncomputable def fixedUniformPaddingGauge
    (P : IndexedGauge s A I)
    (g0 : G) (hfixed : s g0 = g0)
    (M : ℕ) (j : A → Fin M) :
    IndexedGauge s (I × Fin M) I where
  label := Prod.fst
  skeleton := fun _ _ => g0
  skeleton_reverse := by
    intro i k _
    exact hfixed.symm
  vertexGauge := P.fixedUniformPaddingRow j

/-- Every padded E-class is exactly one first-coordinate fibre. -/
theorem fixedUniformPaddingGauge_part
    (P : IndexedGauge s A I)
    (g0 : G) (hfixed : s g0 = g0)
    (M : ℕ) (j : A → Fin M)
    (z w : I × Fin M) :
    (P.fixedUniformPaddingGauge g0 hfixed M j).toEffectiveGeometry.part
      z w ↔ z.1 = w.1 := Iff.rfl

/-- Every diagonal gauge coordinate of the fixed padding is 1,
including at labels which are not images of old vertices. -/
theorem fixedUniformPaddingGauge_diagonal
    (P : IndexedGauge s A I)
    (g0 : G) (hfixed : s g0 = g0)
    (M : ℕ) (j : A → Fin M)
    (w : I × Fin M) :
    (P.fixedUniformPaddingGauge g0 hfixed M j).vertexGauge w w.1 = 1 := by
  simp [fixedUniformPaddingGauge, fixedUniformPaddingRow]

/-- The original effective E-relation is preserved and reflected
exactly on the fixed injection into the padded carrier. -/
theorem fixedUniformPaddingOldMap_part
    (P : IndexedGauge s A I)
    (g0 : G) (hfixed : s g0 = g0)
    (M : ℕ) (j : A → Fin M) (x y : A) :
    (P.fixedUniformPaddingGauge g0 hfixed M j).toEffectiveGeometry.part
      (P.fixedUniformPaddingOldMap j x)
      (P.fixedUniformPaddingOldMap j y) ↔
        P.toEffectiveGeometry.part x y := Iff.rfl

/-- If the ORIGINAL skeleton was also this prechosen constant g0,
the fixed padded geometry retains every original cross-E colour,
with the noncommutative/affine gauge formula unchanged. -/
theorem fixedUniformPaddingOldMap_colour
    (P : IndexedGauge s A I)
    (g0 : G) (hfixed : s g0 = g0)
    (hConstant : ∀ i k : I, P.skeleton i k = g0)
    (M : ℕ) (j : A → Fin M)
    (hj : Function.Injective j)
    (x y : A) (hxy : P.label x ≠ P.label y) :
    (P.fixedUniformPaddingGauge g0 hfixed M j).toEffectiveGeometry.F
      (P.fixedUniformPaddingOldMap j x)
      (P.fixedUniformPaddingOldMap j y) =
        P.toEffectiveGeometry.F x y := by
  have hcross :
      (P.fixedUniformPaddingGauge g0 hfixed M j).label
        (P.fixedUniformPaddingOldMap j x) ≠
      (P.fixedUniformPaddingGauge g0 hfixed M j).label
        (P.fixedUniformPaddingOldMap j y) := hxy
  have hrev : P.label y ≠ P.label x := hxy.symm
  calc
    (P.fixedUniformPaddingGauge g0 hfixed M j).toEffectiveGeometry.F
      (P.fixedUniformPaddingOldMap j x)
      (P.fixedUniformPaddingOldMap j y) =
      gaugeColour s
        (P.fixedUniformPaddingRow j (P.fixedUniformPaddingOldMap j x)
          (P.label y))
        g0
        (P.fixedUniformPaddingRow j (P.fixedUniformPaddingOldMap j y)
          (P.label x)) := by
            exact (P.fixedUniformPaddingGauge g0 hfixed M j)
              .effective_cross _ _ hcross
    _ = gaugeColour s (P.vertexGauge x (P.label y)) g0
        (P.vertexGauge y (P.label x)) := by
          rw [P.fixedUniformPaddingRow_old j hj x (P.label y) hxy,
            P.fixedUniformPaddingRow_old j hj y (P.label x) hrev]
    _ = gaugeColour s (P.vertexGauge x (P.label y))
          (P.skeleton (P.label x) (P.label y))
          (P.vertexGauge y (P.label x)) := by
            rw [hConstant (P.label x) (P.label y)]
    _ = P.toEffectiveGeometry.F x y :=
      (P.effective_cross x y hxy).symm

end IndexedGauge

end SemigenericEPPA
