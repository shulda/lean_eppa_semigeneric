import SemigenericEPPA.Algebra.DLFExplicitSeedSelectedMultipliers
import SemigenericEPPA.Valuations.SelectedExplicitRelativeEffectiveHAction

/-!
# An actual selected H-action with an EXPLICIT globally fixed seed

For relative DLF the complete good congruence orbit is associated
to ONE specially selected colour g0. The coherent-EPPA API uses
Classical.choose of merely a good nonempty set, and that arbitrary
choice is mathematically insufficient for the weaker DLF theorem.

Reuse the exact certified construction of canonical occupied group
multipliers, strict reference-indexed H-action, same-data selected
old zero-section, and full effective E/F invariance, but with g0
supplied explicitly and s(g0)=g0. No separate old-row, cocycle,
or prescribed multiplier assumption. This will allow the selected
relative involution safety theorem to use the SAME chosen complete
good orbit and the SAME genuine full witness action.

The full two-layer witness is not independently changed here.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w}
variable {H : Type t} [Group H]
variable {d : RawDatum G C}

theorem IndexedGauge.exists_selectedExplicitRelativeEffectiveHAction_of_fixedSeed
    (D : EffectiveGeometry d.s V)
    (P : IndexedGauge d.s V (Quotient D.part))
    (hPLabel : ∀ x : V, P.label x = Quotient.mk D.part x)
    (g0 : G) (hFixed : d.s g0 = g0)
    (hConst : ∀ i j : Quotient D.part,
      P.skeleton i j = g0)
    (hDiagP : ∀ x : V, P.vertexGauge x (P.label x) = 1)
    (K : EffectiveWitnessSkeleton D)
    (hK : ∀ q r : EffectiveWitnessPart D,
      K.colour q r = g0)
    (S : Set V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (hF : ∀ (h : H) (x y : S),
      P.label x.val ≠ P.label y.val →
      P.toEffectiveGeometry.F (rho h x.val) (rho h y.val) =
        P.toEffectiveGeometry.F x.val y.val) :
    ∃ (M : H → Quotient D.part → Quotient D.part → G)
      (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
      (hMul : ∀ (k h : H) (i j : Quotient D.part),
        M (k * h) i j =
          M k (iota h i) (iota h j) * M h i j),
      let cls : V → Quotient D.part :=
        fun x => Quotient.mk D.part x
      let z : V → Quotient D.part → G :=
        selectedReferenceGauge S cls P.vertexGauge
      let Theta : H →* Equiv.Perm (EffectiveWitnessVertex D) :=
        D.referenceIndexedWitnessAction rho iota z hcls M hOne hMul
      (∀ (h : H) (i : Quotient D.part), M h i i = 1) ∧
      (∀ (h : H) (x : V), x ∈ S →
        ∀ j : Quotient D.part,
          (∃ y : V, y ∈ S ∧ cls y = j) →
          P.vertexGauge (rho h x) (iota h j) =
            M h (cls x) j * P.vertexGauge x j) ∧
      (∀ (h : H) (x : V), x ∈ S →
        Theta h (D.gaugeOldWitnessVertex P.vertexGauge x) =
          D.gaugeOldWitnessVertex P.vertexGauge (rho h x)) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        K.toEffectiveGeometry.part (Theta h X) (Theta h Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        ¬K.toEffectiveGeometry.part X Y →
          K.toEffectiveGeometry.F (Theta h X) (Theta h Y) =
            K.toEffectiveGeometry.F X Y) := by
  have hLabel : ∀ (h : H) (x : S),
      P.label (rho h x.val) = iota h (P.label x.val) := by
    intro h x
    calc
      P.label (rho h x.val) =
          Quotient.mk D.part (rho h x.val) := hPLabel (rho h x.val)
      _ = iota h (Quotient.mk D.part x.val) := hcls h x.val
      _ = iota h (P.label x.val) := by rw [hPLabel x.val]
  obtain ⟨M, hOne, hMul, hVisited, hUnused, hSkel, hDiagM⟩ :=
    P.exists_selectedOldGroupMultipliers_diagonal_of_fixedSeed
      S g0 hFixed hConst hDiagP rho iota hS hLabel hF
  let cls : V → Quotient D.part :=
    fun x => Quotient.mk D.part x
  let z : V → Quotient D.part → G :=
    selectedReferenceGauge S cls P.vertexGauge
  let sigma : H →* Equiv.Perm (EffectiveWitnessPart D) :=
    referenceWitnessPartAction D rho iota z
  let m : H → EffectiveWitnessPart D →
      EffectiveWitnessPart D → G :=
    fun h q r => M h q.1 r.1
  let Theta : H →* Equiv.Perm (EffectiveWitnessVertex D) :=
    D.referenceIndexedWitnessAction rho iota z hcls M hOne hMul
  have hOccRow : ∀ (h : H) (x : V), x ∈ S →
      ∀ j : Quotient D.part,
        (∃ y : V, y ∈ S ∧ cls y = j) →
        M h (cls x) j * P.vertexGauge x j =
          P.vertexGauge (rho h x) (iota h j) := by
    intro h x hx j hj
    have hxVisited : ∃ y : V, y ∈ S ∧ P.label y = j := by
      rcases hj with ⟨y, hy, hyj⟩
      exact ⟨y, hy, (hPLabel y).trans hyj⟩
    have hRow := hVisited h x hx j hxVisited
    rw [hPLabel x] at hRow
    exact hRow
  have hUnusedRow : ∀ (h : H) (i j : Quotient D.part),
      (¬∃ y : V, y ∈ S ∧ cls y = j) →
        M h i j = 1 := by
    intro h i j hj
    apply hUnused h i j
    rintro ⟨y, hy, hyj⟩
    apply hj
    exact ⟨y, hy, (hPLabel y).symm.trans hyj⟩
  have hOneW :
      ∀ q r : EffectiveWitnessPart D, q ≠ r → m 1 q r = 1 := by
    intro q r _
    exact hOne q.1 r.1
  have hMulW : ∀ (k h : H) (q r : EffectiveWitnessPart D),
      q ≠ r →
      m (k * h) q r =
        m k (sigma h q) (sigma h r) * m h q r := by
    intro k h q r _
    change M (k * h) q.1 r.1 =
      M k (sigma h q).1 (sigma h r).1 * M h q.1 r.1
    rw [referenceWitnessPartAction_class D rho iota z h q,
      referenceWitnessPartAction_class D rho iota z h r]
    exact hMul k h q.1 r.1
  have hSkelW : ∀ (h : H) (q r : EffectiveWitnessPart D),
      q ≠ r →
      d.s.normalized (m h q r) *
        (K.colour (sigma h q) (sigma h r))⁻¹ *
        m h r q = (K.colour q r)⁻¹ := by
    intro h q r _
    change d.s.normalized (M h q.1 r.1) *
      (K.colour (sigma h q) (sigma h r))⁻¹ *
        M h r.1 q.1 = (K.colour q r)⁻¹
    rw [hK (sigma h q) (sigma h r), hK q r]
    exact hSkel h q.1 r.1
  have hSource : ∀ (h : H) (x : V), x ∈ S →
      ∀ y : V,
        z (rho h y) (iota h (cls x)) = z y (cls x) := by
    intro h x hx y
    exact selectedReferenceGauge_visited_source
      S cls P.vertexGauge rho iota hS hcls h x y hx
  have hRow : ∀ (h : H) (x : V), x ∈ S →
      ∀ j : Quotient D.part,
        M h (cls x) j * P.vertexGauge x j =
          P.vertexGauge (rho h x) (iota h j) *
            referenceGaugeTwist rho iota z h x j := by
    intro h x hx j
    exact selectedReferenceGauge_old_row
      S cls P.vertexGauge rho iota hS hcls
      M hOccRow hUnusedRow h x hx j
  have hOld : ∀ (h : H) (x : V), x ∈ S →
      Theta h (D.gaugeOldWitnessVertex P.vertexGauge x) =
        D.gaugeOldWitnessVertex P.vertexGauge (rho h x) := by
    intro h x hx
    exact D.referenceIndexedWitnessAction_maps_gaugeOld_onSubset
      S P.vertexGauge rho iota z hcls
      M hOne hMul hSource hRow h x hx
  have hPresE : ∀ (h : H) (X Y : EffectiveWitnessVertex D),
      K.toEffectiveGeometry.part (Theta h X) (Theta h Y) ↔
        K.toEffectiveGeometry.part X Y := by
    intro h X Y
    exact (referenceWitnessCocycleAction_preserves_effective
      D K rho iota z hcls m hOneW hMulW hSkelW h).1 X Y
  have hPresF : ∀ (h : H) (X Y : EffectiveWitnessVertex D),
      ¬K.toEffectiveGeometry.part X Y →
        K.toEffectiveGeometry.F (Theta h X) (Theta h Y) =
          K.toEffectiveGeometry.F X Y := by
    intro h X Y hXY
    exact (referenceWitnessCocycleAction_preserves_effective
      D K rho iota z hcls m hOneW hMulW hSkelW h).2 X Y hXY
  refine ⟨M, hOne, hMul, hDiagM, ?_, hOld, hPresE, hPresF⟩
  intro h x hx j hj
  exact (hOccRow h x hx j hj).symm


end SemigenericEPPA
