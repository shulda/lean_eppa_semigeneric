import SemigenericEPPA.Structure.DLFNegativeRelativeOnePointRawExtensions
import SemigenericEPPA.Bridge.DLFDeltaProfileMovingThirdPoint
import Mathlib.GroupTheory.Perm.Basic

/-!
# A nontrivial effective group forbids within-class involution motion

This is the SECOND geometric half of the negative DLF converse.

Assume every involution-cross-E swap is forbidden in an ambient
full-age homogeneous original-language rectangle M. Then no
involutive original raw automorphism can swap any two DISTINCT
points in the SAME E-class if the effective group G is nontrivial.

For a same-class moved pair b -> a, use a genuine finite
relative old-part clone to obtain a third old vertex c E b.
Choose an invariant finite *set of vertices*
F={a,b,c,T(c)} (it is enough to know these finitely many
coordinates, not an H-action on a larger structure). Use the
relative singleton raw-row lemma to embed a new vertex v with
effective row delta!=1 at a and 1 at every other F vertex.

The certified moving-third-point delta rectangle forces v and
T(v) to be in DIFFERENT E-classes, contradicting the hypothesis
that T has no cross-E transpositions.

No complete-good-orbit, local safe finite group action or
preservation of the fresh singleton vertex is assumed here.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Nontrivial G]
variable {C : Type v} {V : Type w}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Under age-universality/homogeneity and the exclusion of all
cross-E involutive transpositions, a raw involution cannot move
a point to a different point of its OWN E-class. -/
theorem no_withinPartInvolution_swap_of_noCrossSwap
    (M : RawRectanglePresentation d V)
    (hAge : ∀ (W : Type w) [Fintype W]
      (Q : RawRectanglePresentation d W),
      ∃ t : W → V,
        Function.Injective t ∧
        (∀ x y : W, M.part (t x) (t y) ↔ Q.part x y) ∧
        (∀ x y : W, M.colour (t x) (t y) = Q.colour x y))
    (hHom : ∀ (K : Finset V) (p : K → V),
      Function.Injective p →
      (∀ x y : K, M.part (p x) (p y) ↔ M.part x.val y.val) →
      (∀ x y : K, M.colour (p x) (p y) = M.colour x.val y.val) →
      ∃ α : M.fullRawAutGroup,
        ∀ x : K, α.val x.val = p x)
    (T : Equiv.Perm V)
    (hTcolour : ∀ x y : V, M.colour (T x) (T y) = M.colour x y)
    (hTtwo : ∀ z : V, T (T z) = z)
    (hNoCross : ∀ x y : V, ¬M.part x y →
      T x = y → T y = x → False)
    (a b : V) (hab : M.part a b)
    (hne : a ≠ b) (hTb : T b = a) :
    False := by
  classical
  let F₀ : Finset V := {a, b}
  let aa : {x : V // x ∈ F₀} :=
    ⟨a, by simp [F₀]⟩
  obtain ⟨c, hcFresh, hca, _hcCol⟩ :=
    M.exists_freshRelativeOldPartClone_of_fullAge_homogeneous
      hAge hHom F₀ aa
  have hcaNe : c ≠ a := by
    intro h
    apply hcFresh
    simp [F₀, h]
  have hcbNe : c ≠ b := by
    intro h
    apply hcFresh
    simp [F₀, h]
  have hbc : M.part b c :=
    M.part_equiv.trans (M.part_equiv.symm hab)
      (M.part_equiv.symm hca)
  have hbNea : b ≠ a := Ne.symm hne
  have hTca : T c ≠ a := by
    intro h
    apply hcbNe
    apply T.injective
    exact h.trans hTb.symm
  obtain ⟨delta, hdelta⟩ := exists_ne (1 : G)
  obtain ⟨cdelta, hcdelta⟩ := d.phi_surjective delta
  obtain ⟨cone, hcone⟩ := d.phi_surjective 1
  let F : Finset V := {a, b, c, T c}
  let f : {x : V // x ∈ F} → C :=
    fun x => if x.val = a then cdelta else cone
  obtain ⟨v, hCross, hRaw⟩ :=
    M.exists_relativeSingletonRawRow_of_fullAge_homogeneous
      hAge hHom F f
  have hF (u : V) (hu : u ∈ F) :
      M.effectiveReduct.F v u = if u = a then delta else 1 := by
    let uu : {x : V // x ∈ F} := ⟨u, hu⟩
    have hc : M.colour v u = some (f uu) := hRaw uu
    calc
      M.effectiveReduct.F v u = d.phi (f uu) :=
        (M.effectiveReduct_crossColour v u (f uu) hc).symm
      _ = if u = a then delta else 1 := by
        by_cases h : u = a <;>
          simp [f, uu, h, hcdelta, hcone]
  have hF_a : M.effectiveReduct.F v a = delta := by
    simpa using hF a (by simp [F])
  have hF_b : M.effectiveReduct.F v b = 1 := by
    simpa [hbNea] using hF b (by simp [F])
  have hF_c : M.effectiveReduct.F v c = 1 := by
    simpa [hcaNe] using hF c (by simp [F])
  have hF_Tc : M.effectiveReduct.F v (T c) = 1 := by
    simpa [hTca] using hF (T c) (by simp [F])
  have hCrossVa : ¬M.part v a :=
    hCross ⟨a, by simp [F]⟩
  have hNewCross : ¬M.part v (T v) :=
    M.deltaProfile_forces_crossPart_movingThird
      T hTcolour a b c v hbc hCrossVa hTb
      delta hdelta hF_a hF_b hF_c hF_Tc
  exact hNoCross v (T v) hNewCross rfl (hTtwo v)

end RawRectanglePresentation
end SemigenericEPPA
