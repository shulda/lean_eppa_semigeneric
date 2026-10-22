import SemigenericEPPA.Algebra.SelectedOldGroupMultipliers

/-!
# Canonical selected H-multipliers are literally 1 on all diagonals

The selected-substructure multiplier construction is already
certified to provide a strict noncommutative cocycle on all indices
and affine skeleton equations. To apply the raw flip-safety theorem
to actual same-old-index witness pairs, one further property is
needed: M_h(i,i)=1 for ALL h and i, occupied or not.

This is true for the genuinely constructed canonical neutral
completion, but is NOT a logical consequence of the other
existential multiplier equations alone. In particular, no
arbitrary existentially returned M may be presumed normalized.

This strengthened existence theorem reconstructs the SAME actual
canonical occupied multipliers and proves their neutral diagonal
directly. It preserves the old public existence API unchanged,
and explicitly records all certified selected-substructure group
laws, visited-target rows, unused-target neutrality, affine
skeleton compatibility, and now neutral diagonals simultaneously.
-/

namespace SemigenericEPPA

universe u v w t q
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {I : Type t}
variable {H : Type q} [Group H]
variable {d : RawDatum G C}

namespace IndexedGauge

/-- The concrete original-group multiplier M on old E-indices is
produced from the restricted actual H-action on S. Every assumption
on the old F-matrix is quantified ONLY over vertices in S.

The fixed skeleton value is g0=Classical.choose(hGood), and the
original P.skeleton must already be this constant: it is the global
fixed-witness normal form, not a new S-dependent skeleton choice. -/
theorem exists_selectedOldGroupMultipliers_diagonal
    (P : IndexedGauge d.s V I)
    (S : Set V)
    (hGood : d.selfReverseEffective.Nonempty)
    (hConstant : ∀ i j : I,
      P.skeleton i j = Classical.choose hGood)
    (hDiagonal : ∀ x : V,
      P.vertexGauge x (P.label x) = 1)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (hS : ∀ (h : H) (x : V),
      x ∈ S ↔ rho h x ∈ S)
    (hLabel : ∀ (h : H) (x : S),
      P.label (rho h x.val) = iota h (P.label x.val))
    (hF : ∀ (h : H) (x y : S),
      P.label x.val ≠ P.label y.val →
      P.toEffectiveGeometry.F (rho h x.val) (rho h y.val) =
        P.toEffectiveGeometry.F x.val y.val) :
    ∃ M : H → I → I → G,
      (∀ i j : I, M 1 i j = 1) ∧
      (∀ (k h : H) (i j : I),
        M (k * h) i j =
          M k (iota h i) (iota h j) * M h i j) ∧
      (∀ (h : H) (x : V), x ∈ S →
        ∀ j : I, (∃ y : V, y ∈ S ∧ P.label y = j) →
          M h (P.label x) j * P.vertexGauge x j =
            P.vertexGauge (rho h x) (iota h j)) ∧
      (∀ (h : H) (i j : I),
        (¬∃ y : V, y ∈ S ∧ P.label y = j) →
          M h i j = 1) ∧
      (∀ (h : H) (i j : I),
        d.s.normalized (M h i j) *
          (Classical.choose hGood)⁻¹ *
          M h j i = (Classical.choose hGood)⁻¹) ∧
      (∀ (h : H) (i : I), M h i i = 1) := by
  let Q : IndexedGauge d.s S I := P.restrictSubset S
  let rhoS : H →* Equiv.Perm S := selectedSubsetAction S rho hS
  obtain ⟨hLabelS, hEffectiveS⟩ :=
    P.restrictSubset_H_data S rho iota hS hLabel hF
  let M : H → I → I → G := Q.oldActionMultipliers rhoS iota
  obtain ⟨hOne, hMul⟩ :=
    Q.oldActionMultipliers_group_laws rhoS iota hLabelS hEffectiveS
  have hDiagS : ∀ x : S, Q.vertexGauge x (Q.label x) = 1 := by
    intro x
    exact hDiagonal x.val
  have hRows : ∀ (h : H) (x : V), x ∈ S →
      ∀ (j : I), (∃ y : V, y ∈ S ∧ P.label y = j) →
        M h (P.label x) j * P.vertexGauge x j =
          P.vertexGauge (rho h x) (iota h j) := by
    intro h x hx j hj
    have hjQ : Q.occupied j := by
      obtain ⟨y, hy, hyj⟩ := hj
      exact ⟨⟨y, hy⟩, hyj⟩
    have hr := Q.oldActionMultipliers_transport_all_occupied
      rhoS iota hLabelS hEffectiveS hDiagS
      h (⟨x, hx⟩ : S) j hjQ
    exact hr
  have hUnused : ∀ (h : H) (i j : I),
      (¬∃ y : V, y ∈ S ∧ P.label y = j) → M h i j = 1 := by
    intro h i j hj
    have hjQ : ¬Q.occupied j := by
      rintro ⟨y, hyj⟩
      exact hj ⟨y.val, y.property, hyj⟩
    have hbad : ¬(Q.occupied i ∧ Q.occupied j ∧ i ≠ j) := by
      rintro ⟨_, hi, _⟩
      exact hjQ hi
    change completeOccupiedGaugeMultipliers Q.occupied
      (occupiedGaugeActionMultiplier rhoS iota Q.label Q.vertexGauge)
        h i j = 1
    exact completeOccupiedGaugeMultipliers_default
      Q.occupied
      (occupiedGaugeActionMultiplier rhoS iota Q.label Q.vertexGauge)
      h i j hbad
  have hFixed (i j : I) :
      Q.fixedGoodSkeleton hGood i j = Classical.choose hGood := by
    by_cases hp : Q.occupied i ∧ Q.occupied j ∧ i ≠ j
    · rw [Q.fixedGoodSkeleton_old hGood i j hp.1 hp.2.1 hp.2.2]
      exact hConstant i j
    · change completeOccupiedSkeleton Q.occupied Q.skeleton
          (Classical.choose hGood) i j = Classical.choose hGood
      exact completeOccupiedSkeleton_default
        Q.occupied Q.skeleton (Classical.choose hGood) i j hp
  have hSkeleton : ∀ (h : H) (i j : I),
      d.s.normalized (M h i j) *
        (Classical.choose hGood)⁻¹ *
        M h j i = (Classical.choose hGood)⁻¹ := by
    intro h i j
    have hs := Q.fixedGoodSkeleton_preserved_all
      hGood rhoS iota hLabelS hEffectiveS h i j
    rw [hFixed (iota h i) (iota h j), hFixed i j] at hs
    exact hs
  have hNeutralDiag : ∀ (h : H) (i : I), M h i i = 1 := by
    intro h i
    have hBad : ¬(Q.occupied i ∧ Q.occupied i ∧ i ≠ i) := by
      rintro ⟨_, _, hne⟩
      exact hne rfl
    change completeOccupiedGaugeMultipliers Q.occupied
      (occupiedGaugeActionMultiplier rhoS iota Q.label Q.vertexGauge)
        h i i = 1
    exact completeOccupiedGaugeMultipliers_default
      Q.occupied
      (occupiedGaugeActionMultiplier rhoS iota Q.label Q.vertexGauge)
      h i i hBad
  exact ⟨M, hOne, hMul, hRows, hUnused, hSkeleton, hNeutralDiag⟩

end IndexedGauge

end SemigenericEPPA
