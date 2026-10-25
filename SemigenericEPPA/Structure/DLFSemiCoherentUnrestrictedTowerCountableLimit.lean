import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerDirectedLimits
import Mathlib.Basic.Countable.Basic

/-!
# Unrestricted semi-coherent action-tower colimit: CountableLimit

Port of the verified original-raw finite stage/group-limit theorem
from finite SAFE action pairs to arbitrary finite group-action pairs.
Only injective original E/R_c embeddings and strict equivariant
finite group homomorphisms are required. No local safety hypothesis.
The next modules will construct the actual limit action and density.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteRawActionPairTower

/-- Any genuine countable tower of finite raw structures has an
actual countable quotient vertex carrier. -/
theorem countable_vertexLimit (T : FiniteRawActionPairTower d V) :
    Countable T.VertexLimit := by
  classical
  letI : ∀ n : ℕ, Countable (V n) := fun n => inferInstance
  have hSigma : Countable (Σ n : ℕ, V n) := inferInstance
  have hSurj : Function.Surjective
      (fun a : Σ n : ℕ, V n =>
        (⟦a⟧ : T.VertexLimit)) := by
    intro x
    obtain ⟨n, a, hx⟩ :=
      DirectLimit.exists_eq_mk (f := T.vertexTransition) x
    exact ⟨⟨n, a⟩, hx.symm⟩
  exact hSurj.countable

end FiniteRawActionPairTower
end SemigenericEPPA
