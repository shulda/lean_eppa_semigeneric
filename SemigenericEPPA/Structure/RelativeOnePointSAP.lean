import SemigenericEPPA.Structure.OnePointNormalization
import SemigenericEPPA.Structure.LiteralSAPEmbeddings

/-!
# Strong one-point SAP with arbitrarily named finite carriers

The previous theorem handles two one-point extensions on the canonical
carrier Option X. Here each side can instead use its own carrier Y or Z
and an arbitrary injective embedding of the common old carrier X.

Assuming that each side consists *exactly* of its old vertices and one
genuinely fresh vertex, we normalize both sides through the verified
onePointCarrierEquiv, apply literal one-point SAP, and transport the
resulting embeddings back. Their images overlap *exactly* on the
common old vertices. No artificial common naming or extra linear
order appears in the statement.

This is a reusable one-point pushout API for iterating SAP over finite
diagrams, not yet the final arbitrary finite SAP theorem.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t q

variable {G : Type u} [Group G] {C : Type v}

/-- An arbitrary pair of literal one-point R1–R3 extensions. The old
vertex injections need not be inclusions, and the two side vertex
types need not coincide. -/
structure RelativeOnePointDiagram (d : RawDatum G C)
    (X : Type w) (Y : Type z) (Z : Type t) where
  base : Structure (rectangleLanguage C) X
  left : Structure (rectangleLanguage C) Y
  right : Structure (rectangleLanguage C) Z
  baseValid : IsRectangleStructure d base
  leftValid : IsRectangleStructure d left
  rightValid : IsRectangleStructure d right
  leftOld : X → Y
  rightOld : X → Z
  leftInjective : Function.Injective leftOld
  rightInjective : Function.Injective rightOld
  leftFresh : Y
  rightFresh : Z
  leftFreshOutside : ∀ a, leftOld a ≠ leftFresh
  rightFreshOutside : ∀ a, rightOld a ≠ rightFresh
  leftCover : ∀ y, y = leftFresh ∨ ∃ a, leftOld a = y
  rightCover : ∀ z, z = rightFresh ∨ ∃ a, rightOld a = z
  leftPart : ∀ a b,
    partRel left (leftOld a) (leftOld b) ↔ partRel base a b
  rightPart : ∀ a b,
    partRel right (rightOld a) (rightOld b) ↔ partRel base a b
  leftRaw : ∀ c : C, ∀ a b,
    rawRel left c (leftOld a) (leftOld b) ↔ rawRel base c a b
  rightRaw : ∀ c : C, ∀ a b,
    rawRel right c (rightOld a) (rightOld b) ↔ rawRel base c a b

namespace RelativeOnePointDiagram

variable {d : RawDatum G C}
variable {X : Type w} {Y : Type z} {Z : Type t}
variable (Q : RelativeOnePointDiagram d X Y Z)

/-- The exact normalization of the left carrier to Option X. -/
noncomputable def leftCarrierEquiv : Option X ≃ Y :=
  onePointCarrierEquiv Q.leftOld Q.leftInjective
    Q.leftFresh Q.leftFreshOutside Q.leftCover

/-- The exact normalization of the right carrier to Option X. -/
noncomputable def rightCarrierEquiv : Option X ≃ Z :=
  onePointCarrierEquiv Q.rightOld Q.rightInjective
    Q.rightFresh Q.rightFreshOutside Q.rightCover

/-- Reindexed left literal structure, with the new vertex at none. -/
noncomputable def leftNormalized :
    Structure (rectangleLanguage C) (Option X) :=
  pullbackRectangle Q.left Q.leftCarrierEquiv

/-- Reindexed right literal structure, with the new vertex at none. -/
noncomputable def rightNormalized :
    Structure (rectangleLanguage C) (Option X) :=
  pullbackRectangle Q.right Q.rightCarrierEquiv

/-- The canonical one-point diagram obtained without any change of
the underlying relational mathematics. -/
noncomputable def normalizedDiagram : LiteralOnePointDiagram d X where
  base := Q.base
  left := Q.leftNormalized
  right := Q.rightNormalized
  baseValid := Q.baseValid
  leftValid := Q.leftValid.pullback Q.leftCarrierEquiv
  rightValid := Q.rightValid.pullback Q.rightCarrierEquiv
  left_part := by
    intro a b
    exact (pullback_partRel Q.left Q.leftCarrierEquiv (some a) (some b)).trans
      (by simpa using Q.leftPart a b)
  right_part := by
    intro a b
    exact (pullback_partRel Q.right Q.rightCarrierEquiv (some a) (some b)).trans
      (by simpa using Q.rightPart a b)
  left_raw := by
    intro c a b
    exact (pullback_rawRel Q.left Q.leftCarrierEquiv c (some a) (some b)).trans
      (by simpa using Q.leftRaw c a b)
  right_raw := by
    intro c a b
    exact (pullback_rawRel Q.right Q.rightCarrierEquiv c (some a) (some b)).trans
      (by simpa using Q.rightRaw c a b)

/-- An equivalence-based pullback is isomorphic to the original
structure, in *both* directions as genuine upstream embeddings. -/
def inversePullbackEmbedding
    {Γ : Type q} [Group Γ]
    (act : (rectangleLanguage C).Action Γ)
    {U : Type*} {T : Type*}
    (B : Structure (rectangleLanguage C) T)
    (e : U ≃ T) :
    Structure.Embedding act B (pullbackRectangle B e) where
  lang := 1
  toFun := e.symm
  injective := e.symm.injective
  map_rel_iff := by
    intro n R xs
    simp only [Language.Action.onRel_one]
    change B.rel R (e ∘ (e.symm ∘ xs)) ↔ B.rel R xs
    have heq : e ∘ (e.symm ∘ xs) = xs := by
      funext i
      simp [Function.comp_def]
    rw [heq]
  map_func := by
    intro n F xs
    exact PEmpty.elim F

/-- Strong one-point SAP with arbitrary source vertex names, returning
real upstream embeddings. The common old base is exactly the
intersection of their images; no new vertices are identified. -/
theorem finite_relative_onePoint_strong_amalgamation
    [Fintype X]
    {Γ : Type q} [Group Γ]
    (act : (rectangleLanguage C).Action Γ) :
    ∃ S : Structure (rectangleLanguage C) (TwoPointCarrier X),
      IsRectangleStructure d S ∧
      ∃ (f : Structure.Embedding act Q.left S)
        (g : Structure.Embedding act Q.right S),
        (∀ a : X, f (Q.leftOld a) = firstOnePoint (some a)) ∧
        (∀ a : X, g (Q.rightOld a) = secondOnePoint (some a)) ∧
        f Q.leftFresh = firstOnePoint none ∧
        g Q.rightFresh = secondOnePoint none ∧
        (∀ y : Y, ∀ z : Z,
          f y = g z ↔
            ∃ a : X, y = Q.leftOld a ∧ z = Q.rightOld a) ∧
        (∀ w : TwoPointCarrier X,
          (∃ y : Y, f y = w) ∨ (∃ z : Z, g z = w)) := by
  let eL : Option X ≃ Y := Q.leftCarrierEquiv
  let eR : Option X ≃ Z := Q.rightCarrierEquiv
  have heL : ∀ a : X, eL.symm (Q.leftOld a) = some a := by
    intro a
    have h : eL (some a) = Q.leftOld a :=
      onePointCarrierEquiv_some Q.leftOld Q.leftInjective
        Q.leftFresh Q.leftFreshOutside Q.leftCover a
    rw [← h]
    exact eL.symm_apply_apply (some a)
  have heR : ∀ a : X, eR.symm (Q.rightOld a) = some a := by
    intro a
    have h : eR (some a) = Q.rightOld a :=
      onePointCarrierEquiv_some Q.rightOld Q.rightInjective
        Q.rightFresh Q.rightFreshOutside Q.rightCover a
    rw [← h]
    exact eR.symm_apply_apply (some a)
  have heLnone : eL.symm Q.leftFresh = none := by
    have h : eL none = Q.leftFresh :=
      onePointCarrierEquiv_none Q.leftOld Q.leftInjective
        Q.leftFresh Q.leftFreshOutside Q.leftCover
    rw [← h]
    exact eL.symm_apply_apply none
  have heRnone : eR.symm Q.rightFresh = none := by
    have h : eR none = Q.rightFresh :=
      onePointCarrierEquiv_none Q.rightOld Q.rightInjective
        Q.rightFresh Q.rightFreshOutside Q.rightCover
    rw [← h]
    exact eR.symm_apply_apply none
  obtain ⟨S, hS, fNorm, gNorm, hfn, hgn, hinter⟩ :=
    Q.normalizedDiagram.finite_onePoint_strong_amalgamation_embeddings act
  let f : Structure.Embedding act Q.left S :=
    fNorm.comp (inversePullbackEmbedding act Q.left eL)
  let g : Structure.Embedding act Q.right S :=
    gNorm.comp (inversePullbackEmbedding act Q.right eR)
  refine ⟨S, hS, f, g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    change fNorm (eL.symm (Q.leftOld a)) = firstOnePoint (some a)
    rw [heL a]
    exact hfn (some a)
  · intro a
    change gNorm (eR.symm (Q.rightOld a)) = secondOnePoint (some a)
    rw [heR a]
    exact hgn (some a)
  · change fNorm (eL.symm Q.leftFresh) = firstOnePoint none
    rw [heLnone]
    exact hfn none
  · change gNorm (eR.symm Q.rightFresh) = secondOnePoint none
    rw [heRnone]
    exact hgn none
  · intro y z
    constructor
    · intro h
      have h' :
          fNorm (eL.symm y) = gNorm (eR.symm z) := h
      obtain ⟨a, ha, hb⟩ :=
        (hinter (eL.symm y) (eR.symm z)).mp h'
      refine ⟨a, ?_, ?_⟩
      · calc
          y = eL (eL.symm y) := (eL.apply_symm_apply y).symm
          _ = eL (some a) := congrArg eL ha
          _ = Q.leftOld a := by
            exact onePointCarrierEquiv_some Q.leftOld Q.leftInjective
              Q.leftFresh Q.leftFreshOutside Q.leftCover a
      · calc
          z = eR (eR.symm z) := (eR.apply_symm_apply z).symm
          _ = eR (some a) := congrArg eR hb
          _ = Q.rightOld a := by
            exact onePointCarrierEquiv_some Q.rightOld Q.rightInjective
              Q.rightFresh Q.rightFreshOutside Q.rightCover a
    · rintro ⟨a, ha, hb⟩
      change fNorm (eL.symm y) = gNorm (eR.symm z)
      rw [ha, hb, heL a, heR a]
      exact (hinter (some a) (some a)).2 ⟨a, rfl, rfl⟩
  · intro w
    cases w with
    | inl a =>
      left
      refine ⟨Q.leftOld a, ?_⟩
      change fNorm (eL.symm (Q.leftOld a)) = firstOnePoint (some a)
      rw [heL a]
      exact hfn (some a)
    | inr flag =>
      cases flag with
      | false =>
        left
        refine ⟨Q.leftFresh, ?_⟩
        change fNorm (eL.symm Q.leftFresh) = firstOnePoint none
        rw [heLnone]
        exact hfn none
      | true =>
        right
        refine ⟨Q.rightFresh, ?_⟩
        change gNorm (eR.symm Q.rightFresh) = secondOnePoint none
        rw [heRnone]
        exact hgn none

end RelativeOnePointDiagram
end SemigenericEPPA
