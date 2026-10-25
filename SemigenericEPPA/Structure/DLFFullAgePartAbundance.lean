import SemigenericEPPA.Structure.DLFNegativeRelativeOnePointRawExtensions
import SemigenericEPPA.Structure.DLFNormalizeFiniteRawToFin

/-!
# Full finite age and homogeneity force unbounded E-class abundance

Independently of any DLF or good-colour condition, a raw
R1--R3 structure with the full canonical finite age and
finite-partial ultrahomogeneity admits the exact relative
one-point extension property for two elementary patterns.

* Any finite old set F can be avoided by a whole NEW E-class:
  add a singleton whose original raw colours to each old
  vertex can be chosen freely.
* Every E-class containing an old vertex x can be enlarged
  OUTSIDE any prescribed finite set F, retaining the exact
  original raw profile of x toward F.

These are the precise finite-avoidance formulations that all
E-classes are infinite and there are infinitely many E-classes.
No Sagi theorem, Fraisse uniqueness, or good-colour condition
is used.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Full canonical finite R1--R3 age and ultrahomogeneity imply
both kinds of arbitrarily large E-part supply, expressed by
finite avoidance on the genuine original raw carrier. -/
theorem freshPart_and_oldPartExpansion_of_fullAge_homogeneous
    (M : RawRectanglePresentation d V)
    (hFin : ∀ (n : ℕ) (P : RawRectanglePresentation d (Fin n)),
      ∃ e : Fin n → V,
        Function.Injective e ∧
        (∀ x y : Fin n,
          M.part (e x) (e y) ↔ P.part x y) ∧
        (∀ x y : Fin n,
          M.colour (e x) (e y) = P.colour x y))
    (hHom : ∀ (F : Finset V) (p : F → V),
      Function.Injective p →
      (∀ x y : F,
        M.part (p x) (p y) ↔ M.part x.val y.val) →
      (∀ x y : F,
        M.colour (p x) (p y) = M.colour x.val y.val) →
      ∃ α : M.fullRawAutGroup,
        ∀ x : F, α.val x.val = p x) :
    (∀ F : Finset V,
      ∃ z : V, z ∉ F ∧
        (∀ x : V, x ∈ F → ¬M.part z x)) ∧
    (∀ (F : Finset V) (x : V), x ∈ F →
      ∃ z : V, z ∉ F ∧ M.part z x) := by
  classical
  have hAge : ∀ (W : Type w) [Fintype W]
      (P : RawRectanglePresentation d W),
      ∃ e : W → V,
        Function.Injective e ∧
        (∀ x y : W, M.part (e x) (e y) ↔ P.part x y) ∧
        (∀ x y : W, M.colour (e x) (e y) = P.colour x y) :=
    M.inducedFiniteAge_of_canonicalFinAge hFin
  constructor
  · intro F
    let c : C := Classical.choose (d.phi_surjective 1)
    obtain ⟨z, hNew, _hRaw⟩ :=
      M.exists_relativeSingletonRawRow_of_fullAge_homogeneous
        hAge hHom F (fun _ => c)
    refine ⟨z, ?_, ?_⟩
    · intro hz
      exact (hNew ⟨z, hz⟩) (M.part_equiv.refl z)
    · intro x hx
      exact hNew ⟨x, hx⟩
  · intro F x hx
    let a : {y : V // y ∈ F} := ⟨x, hx⟩
    obtain ⟨z, hz, hPart, _hRaw⟩ :=
      M.exists_freshRelativeOldPartClone_of_fullAge_homogeneous
        hAge hHom F a
    exact ⟨z, hz, hPart⟩

end RawRectanglePresentation
end SemigenericEPPA
