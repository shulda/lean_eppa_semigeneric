import SemigenericEPPA.Structure.DLFNegativeRelativeRowMultiplier
import SemigenericEPPA.Structure.DLFFullRawAutomorphismGroup
import Mathlib.Data.Finset.Basic

/-!
# An actual global original-language automorphism with a literal two-cycle

The negative DLF parity contradiction must start with a true
automorphism of the ambient full-age ultrahomogeneous M which
swaps two distinct old vertices.

The complete finite raw age includes two vertices in ONE E-class
and no cross-colours. Embed its canonical Bool representative.
Their partial transposition preserves the original E predicate
and every ordered Option-valued raw colour exactly. By genuine
finite-partial-map ultrahomogeneity it extends to an ACTUAL
element of M.fullRawAutGroup exchanging the pair in both
directions.

There is no assumption that this global automorphism is itself
an involution: the later density/local finiteness group lemma
extracts a genuine finite-group involution from its two-cycle.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- A full finite age with original finite-partial ultrahomogeneity
contains a genuine raw automorphism interchanging two DISTINCT
vertices, with no group torsion assumption on that automorphism. -/
theorem exists_fullRawAutomorphism_twoCycle_of_fullAge_homogeneous
    (M : RawRectanglePresentation d V)
    (hAgeSmall : ∀ (W : Type) [Fintype W]
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
        ∀ x : K, α.val x.val = p x) :
    ∃ (x y : V) (a : M.fullRawAutGroup),
      x ≠ y ∧ M.part x y ∧ a.val x = y ∧ a.val y = x := by
  classical
  obtain ⟨j, hj, hjPart, hjColour⟩ :=
    hAgeSmall Bool (fullOnePartBoolRaw d)
  let x : V := j false
  let y : V := j true
  have hne : x ≠ y := by
    intro h
    have hFalse : (false : Bool) = true := hj h
    cases hFalse
  have hab : M.part x y := (hjPart false true).mpr trivial
  let F : Finset V := {x, y}
  let p : F → V := fun z => Equiv.swap x y z.val
  have hFMem (u : V) (hu : u ∈ F) : u = x ∨ u = y := by
    simpa [F] using hu
  have hPart (u v : V) (hu : u ∈ F) (hv : v ∈ F) :
      M.part u v := by
    rcases hFMem u hu with rfl | rfl <;>
      rcases hFMem v hv with rfl | rfl
    · exact M.part_equiv.refl x
    · exact hab
    · exact M.part_equiv.symm hab
    · exact M.part_equiv.refl y
  have hSwapX : (Equiv.swap x y) x = y := by simp
  have hSwapY : (Equiv.swap x y) y = x := by simp
  have hpMem (z : F) : p z ∈ F := by
    rcases hFMem z.val z.property with hx | hy
    · change (Equiv.swap x y) z.val ∈ F
      rw [hx, hSwapX]
      simp [F]
    · change (Equiv.swap x y) z.val ∈ F
      rw [hy, hSwapY]
      simp [F]
  have hpInj : Function.Injective p :=
    (Equiv.swap x y).injective.comp Subtype.val_injective
  have hpPart : ∀ u v : F,
      M.part (p u) (p v) ↔ M.part u.val v.val := by
    intro u v
    constructor
    · intro _
      exact hPart u.val v.val u.property v.property
    · intro _
      exact hPart (p u) (p v) (hpMem u) (hpMem v)
  have hpColour : ∀ u v : F,
      M.colour (p u) (p v) = M.colour u.val v.val := by
    intro u v
    have hl : M.colour (p u) (p v) = none :=
      (M.colour_none_iff (p u) (p v)).2
        (hPart (p u) (p v) (hpMem u) (hpMem v))
    have hr : M.colour u.val v.val = none :=
      (M.colour_none_iff u.val v.val).2
        (hPart u.val v.val u.property v.property)
    exact hl.trans hr.symm
  obtain ⟨a, hExt⟩ := hHom F p hpInj hpPart hpColour
  have hax : a.val x = y := by
    have h := hExt ⟨x, by simp [F]⟩
    simpa only [p, hSwapX] using h
  have hay : a.val y = x := by
    have h := hExt ⟨y, by simp [F]⟩
    simpa only [p, hSwapY] using h
  exact ⟨x, y, a, hne, hab, hax, hay⟩

end RawRectanglePresentation
end SemigenericEPPA
