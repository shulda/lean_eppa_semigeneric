import SemigenericEPPA.Structure.RestrictedIndexedGaugeHAction
import SemigenericEPPA.Algebra.IndexedGaugeFixedGoodHAction
import SemigenericEPPA.Algebra.OccupiedGoodDiagonalFullLaws
import SemigenericEPPA.Algebra.NormalizedDiagonalOldRowTransport

/-!
# Canonical occupied H-multipliers from the selected old substructure

Suppose P is a genuine old indexed E-rectangle geometry with a
CONSTANT skeleton g0 chosen from the good effective set, and its
same-class gauge coordinates are normalized to 1.

A strict group H acts by E/F-automorphisms only on an induced old
subset S. The action is extended to permutations rho of the
auxiliary labels V and iota of their E-indices, preserving S and
the class-index map, but it need NOT preserve effective F outside S.

Restrict the indexed gauge to the actual subtype S and apply the
previously certified occupied gauge multiplier construction there.
It gives ONE canonical total family M_h(i,j):
* strict identity and noncommutative group cocycle, all i,j;
* exact old row transport whenever the TARGET index j meets S,
  INCLUDING the diagonal (thanks to the normalized gauge);
* M_h(i,j)=1 on every unvisited target index j;
* the exact affine skeleton preservation equation for EVERY index
  pair, including old-index diagonals.

The uniform constant g0 skeleton is fixed independently of S/H
and is the SAME global skeleton on all witness parts q=(i,f).
This is the missing finite-group algebraic package for relative
coherent-positive H-actions. No full ambient F-invariance, HKN
black box, recentering, or abelianness is assumed.

The whole two-layer witness action and raw-colour orbit safety
remain subsequent constructions.
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
theorem exists_selectedOldGroupMultipliers
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
          M h j i = (Classical.choose hGood)⁻¹) := by
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
  exact ⟨M, hOne, hMul, hRows, hUnused, hSkeleton⟩

end IndexedGauge

end SemigenericEPPA
