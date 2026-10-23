import SemigenericEPPA.Algebra.SelectedOldGroupMultipliersDiagonal

/-!
# Canonical selected multipliers with an EXPLICIT chosen good seed

The existing certified canonical selected multiplier theorem uses
Classical.choose applied to a mere proof that the good set is
nonempty. Relative DLF is more delicate: ONE PARTICULAR good
effective colour g0 must have its complete congruence orbit inside
the good set. An arbitrary different good seed is not safe.

This theorem reuses the exact original canonical multiplier
construction, with all occupied row/cocycle/diagonal equations,
but takes the fixed s-reversal-fixed seed g0 explicitly instead
of choosing it from a nonempty good set. The affine skeleton
equation is obtained directly from the occupied matrix law and
neutral completion, including the same-old-index diagonal case.

The proof is valid for arbitrary nonabelian G and arbitrary affine
anti-involution s; no global good-set saturation, no s(1)=1,
and no independently postulated multiplier family.
-/

namespace SemigenericEPPA

universe u v w t q
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {I : Type t}
variable {H : Type q} [Group H]
variable {d : RawDatum G C}

namespace IndexedGauge

theorem exists_selectedOldGroupMultipliers_diagonal_of_fixedSeed
    (P : IndexedGauge d.s V I)
    (S : Set V)
    (g0 : G) (hFixed : d.s g0 = g0)
    (hConstant : ∀ i j : I,
      P.skeleton i j = g0)
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
          g0⁻¹ *
          M h j i = g0⁻¹) ∧
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
  have hOcc : ∀ (h : H) (i : I),
      Q.occupied (iota h i) ↔ Q.occupied i := by
    intro h i
    exact occupiedGaugeClass_hInvariant rhoS iota Q.label
      hLabelS h i
  have hMatrix := Q.matrix_invariant_of_effective_H_action
    rhoS iota hLabelS hEffectiveS
  have hMSkeleton : ∀ (h : H) (i j : I),
      Q.occupied i → Q.occupied j → i ≠ j →
      d.s.normalized
          (occupiedGaugeActionMultiplier rhoS iota
            Q.label Q.vertexGauge h i j) *
        (Q.skeleton (iota h i) (iota h j))⁻¹ *
          occupiedGaugeActionMultiplier rhoS iota
            Q.label Q.vertexGauge h j i =
        (Q.skeleton i j)⁻¹ := by
    intro h i j hi hj hij
    exact (occupiedGaugeActionMultiplier_preserves_old_pair
      d.s rhoS iota Q.label Q.vertexGauge Q.skeleton
      hMatrix h i j hi hj hij).2.2
  have hConstantCompleted (i j : I) :
      completeOccupiedSkeleton Q.occupied Q.skeleton g0 i j = g0 := by
    by_cases hp : Q.occupied i ∧ Q.occupied j ∧ i ≠ j
    · rw [completeOccupiedSkeleton_occupied Q.occupied Q.skeleton
        g0 i j hp.1 hp.2.1 hp.2.2]
      exact hConstant i j
    · exact completeOccupiedSkeleton_default
        Q.occupied Q.skeleton g0 i j hp
  have hSkeleton : ∀ (h : H) (i j : I),
      d.s.normalized (M h i j) * g0⁻¹ *
        M h j i = g0⁻¹ := by
    intro h i j
    by_cases hij : i ≠ j
    · have hs := completedOccupiedSkeleton_multiplier_condition
        d.s iota Q.occupied hOcc Q.skeleton g0
        (occupiedGaugeActionMultiplier rhoS iota Q.label Q.vertexGauge)
        hMSkeleton h i j hij
      rw [hConstantCompleted (iota h i) (iota h j),
        hConstantCompleted i j] at hs
      exact hs
    · have heq : i = j := not_ne_iff.mp hij
      subst j
      have hbad : ¬(Q.occupied i ∧ Q.occupied i ∧ i ≠ i) := by
        rintro ⟨_,_,hne⟩
        exact hne rfl
      change d.s.normalized
          (completeOccupiedGaugeMultipliers Q.occupied
            (occupiedGaugeActionMultiplier rhoS iota
              Q.label Q.vertexGauge) h i i) * g0⁻¹ *
          completeOccupiedGaugeMultipliers Q.occupied
            (occupiedGaugeActionMultiplier rhoS iota
              Q.label Q.vertexGauge) h i i = g0⁻¹
      rw [completeOccupiedGaugeMultipliers_default Q.occupied
        (occupiedGaugeActionMultiplier rhoS iota Q.label Q.vertexGauge)
        h i i hbad]
      unfold AffineAntiInvolution.normalized
      group
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
