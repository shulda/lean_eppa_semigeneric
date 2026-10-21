import SemigenericEPPA.Algebra.SelectedOldGroupMultipliers
import SemigenericEPPA.Valuations.SelectedReferenceEffectiveHAction

/-!
# Full effective finite H-action from automorphisms of a selected old S

This assembles the entire algebraic positive coherent finite-group
lift, subject to a genuine compatible action on the AUXILIARY
old real-label and quotient E-index sorts.

Input: an arbitrary normalized old indexed gauge P on V, with its
original E-indices equal to Quotient D.part, and a globally chosen
constant skeleton g0 from the self-reversing raw effective colours.
Only an induced subset S is required to carry H-automorphisms of
the effective matrix. Outside S, the extended label permutation
rho may freely alter the old effective colours.

The canonical multipliers come from the ACTUAL restricted H-action
on P|S and satisfy all noncommutative cocycle and affine skeleton
laws. The selected reference gauge is chosen independently of H
and repairs the unoccupied target columns. On the SAME two-layer
effective valuation carrier, the resulting honest group action
Theta extends every old gauge vertex from S and preserves ALL
effective witness E/F colours.

The fixed skeleton K is selected from d and g0 before S/H and
is literally constant on every pair of witness parts. The
finite divisible padding/replicated-label action and raw-colour
safety/lift are separate remaining gates. No general ambient
H-invariance of old F is imposed.
-/

namespace SemigenericEPPA

universe u v w t q
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {H : Type t} [Group H]
variable {d : RawDatum G C}

/-- Selected-substructure E/F H-actions lift homomorphically on one
constant-good-skeleton effective valuation witness. There are NO
unsupplied M or z hypotheses: both are constructed.

The old vertex embedding used here has arbitrary supplied gauge
rows a=P.vertexGauge and may subsequently be instantiated with
the canonical constant-skeleton recoding of any literal old
rectangle member. Every old vertex of S is mapped exactly, with
all its independent vertex valuation coordinates, not just labels. -/
theorem IndexedGauge.exists_relativeFullEffectiveGroupLift
    (D : EffectiveGeometry d.s V)
    (P : IndexedGauge d.s V (Quotient D.part))
    (hPLabel : ∀ x : V,
      P.label x = Quotient.mk D.part x)
    (S : Set V)
    (hGood : d.selfReverseEffective.Nonempty)
    (hConstant : ∀ i j : Quotient D.part,
      P.skeleton i j = Classical.choose hGood)
    (hDiagonal : ∀ x : V,
      P.vertexGauge x (P.label x) = 1)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hS : ∀ (h : H) (x : V),
      x ∈ S ↔ rho h x ∈ S)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (hF : ∀ (h : H) (x y : S),
      P.label x.val ≠ P.label y.val →
      P.toEffectiveGeometry.F (rho h x.val) (rho h y.val) =
        P.toEffectiveGeometry.F x.val y.val) :
    ∃ (K : EffectiveWitnessSkeleton D)
      (Theta : H →* Equiv.Perm (EffectiveWitnessVertex D)),
      (∀ (q r : EffectiveWitnessPart D),
        K.colour q r = Classical.choose hGood) ∧
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
  obtain ⟨M, hOne, hMul, hOccRows, hUnused, hSkel⟩ :=
    P.exists_selectedOldGroupMultipliers S hGood hConstant
      hDiagonal rho iota hS hLabel hF
  have hOccD : ∀ (h : H) (x : V), x ∈ S →
      ∀ j : Quotient D.part,
        (∃ y : V, y ∈ S ∧ Quotient.mk D.part y = j) →
          M h (Quotient.mk D.part x) j * P.vertexGauge x j =
            P.vertexGauge (rho h x) (iota h j) := by
    intro h x hx j hj
    have hjP : ∃ y : V, y ∈ S ∧ P.label y = j := by
      obtain ⟨y, hy, hyj⟩ := hj
      exact ⟨y, hy, (hPLabel y).trans hyj⟩
    have hr := hOccRows h x hx j hjP
    rw [hPLabel x] at hr
    exact hr
  have hUnusedD : ∀ (h : H) (i j : Quotient D.part),
      (¬∃ y : V, y ∈ S ∧ Quotient.mk D.part y = j) →
        M h i j = 1 := by
    intro h i j hj
    apply hUnused h i j
    rintro ⟨y, hy, hyj⟩
    apply hj
    exact ⟨y, hy, (hPLabel y).symm.trans hyj⟩
  let g0 : G := Classical.choose hGood
  have hFixed : d.s g0 = g0 :=
    d.selfReverseEffective_subset_fixed (Classical.choose_spec hGood)
  let K0 : Quotient D.part → Quotient D.part → G :=
    fun _ _ => g0
  have hReverse : ∀ i j : Quotient D.part,
      K0 j i = d.s (K0 i j) := by
    intro i j
    exact hFixed.symm
  have hSkelD : ∀ (h : H) (i j : Quotient D.part),
      d.s.normalized (M h i j) *
        (K0 (iota h i) (iota h j))⁻¹ *
          M h j i = (K0 i j)⁻¹ := by
    intro h i j
    exact hSkel h i j
  obtain ⟨Theta, hOld, hE, hFNew⟩ :=
    D.exists_selectedReferenceEffectiveHAction
      S P.vertexGauge K0 hReverse rho iota hS hcls M
      hOne hMul hOccD hUnusedD hSkelD
  let K : EffectiveWitnessSkeleton D :=
    D.indexedWitnessSkeleton K0 hReverse
  exact ⟨K, Theta, (fun _ _ => rfl), hOld, hE, hFNew⟩

end SemigenericEPPA
