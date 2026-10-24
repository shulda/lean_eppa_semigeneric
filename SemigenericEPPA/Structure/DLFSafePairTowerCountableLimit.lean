import SemigenericEPPA.Structure.DLFSafePairTowerDirectedLimits
import Mathlib.Basic.Countable.Defs

/-!
# The true quotient vertex limit of finite safe pairs is countable

A genuine ℕ-indexed tower has a finite carrier at every stage.
Every quotient-limit vertex is represented by one point at some
finite stage. Thus the canonical sigma-type of tagged finite
vertices surjects onto the actual vertex direct limit.

This proves that the constructed original-language homogeneous
DLF candidate is COUNTABLE (in the precise Lean Countable sense),
without adding an external countability hypothesis or any
topological assumption.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- Any genuine countable tower of finite raw structures has an
actual countable quotient vertex carrier. -/
theorem countable_vertexLimit (T : FiniteSafeRawPairTower d V) :
    Countable T.VertexLimit := by
  classical
  have hSigma : Countable (Σ n : ℕ, V n) := inferInstance
  have hSurj : Function.Surjective
      (fun a : Σ n : ℕ, V n =>
        (⟦a⟧ : T.VertexLimit)) := by
    intro x
    obtain ⟨n, a, hx⟩ :=
      DirectLimit.exists_eq_mk (f := T.vertexTransition) x
    exact ⟨⟨n, a⟩, hx.symm⟩
  exact hSurj.countable

end FiniteSafeRawPairTower
end SemigenericEPPA
