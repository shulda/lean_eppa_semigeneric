import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitRawLaws

/-!
# Unrestricted semi-coherent action-tower colimit: LimitRawRectangle

Port of the verified original-raw finite stage/group-limit theorem
from finite SAFE action pairs to arbitrary finite group-action pairs.
Only injective original E/R_c embeddings and strict equivariant
finite group homomorphisms are required. No local safety hypothesis.
The next modules will construct the actual limit action and density.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G] {C : Type v} [Finite C]
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteRawActionPairTower

/-- Any FOUR elements of the actual quotient vertex limit have
representatives in a single old finite stage, with no identification
or reliance on a common choice of raw-gauge parameters. -/
theorem exists_four_at_sameStage
    (T : FiniteRawActionPairTower d V)
    (x₀ x₁ y₀ y₁ : T.VertexLimit) :
    ∃ (n : ℕ) (a b c e : V n),
      x₀ = T.vertexOf n a ∧
      x₁ = T.vertexOf n b ∧
      y₀ = T.vertexOf n c ∧
      y₁ = T.vertexOf n e := by
  obtain ⟨i₀, a₀, ha₀⟩ :=
    DirectLimit.exists_eq_mk (f := T.vertexTransition) x₀
  obtain ⟨i₁, a₁, ha₁⟩ :=
    DirectLimit.exists_eq_mk (f := T.vertexTransition) x₁
  obtain ⟨j₀, b₀, hb₀⟩ :=
    DirectLimit.exists_eq_mk (f := T.vertexTransition) y₀
  obtain ⟨j₁, b₁, hb₁⟩ :=
    DirectLimit.exists_eq_mk (f := T.vertexTransition) y₁
  let n : ℕ := max (max i₀ i₁) (max j₀ j₁)
  have hi₀ : i₀ ≤ n :=
    (le_max_left i₀ i₁).trans (le_max_left (max i₀ i₁) (max j₀ j₁))
  have hi₁ : i₁ ≤ n :=
    (le_max_right i₀ i₁).trans (le_max_left (max i₀ i₁) (max j₀ j₁))
  have hj₀ : j₀ ≤ n :=
    (le_max_left j₀ j₁).trans (le_max_right (max i₀ i₁) (max j₀ j₁))
  have hj₁ : j₁ ≤ n :=
    (le_max_right j₀ j₁).trans (le_max_right (max i₀ i₁) (max j₀ j₁))
  refine ⟨n, T.vertexTransition i₀ n hi₀ a₀,
    T.vertexTransition i₁ n hi₁ a₁,
    T.vertexTransition j₀ n hj₀ b₀,
    T.vertexTransition j₁ n hj₁ b₁, ?_, ?_, ?_, ?_⟩
  · exact ha₀.trans (T.vertexOf_transition i₀ n hi₀ a₀).symm
  · exact ha₁.trans (T.vertexOf_transition i₁ n hi₁ a₁).symm
  · exact hb₀.trans (T.vertexOf_transition j₀ n hj₀ b₀).symm
  · exact hb₁.trans (T.vertexOf_transition j₁ n hj₁ b₁).symm

/-- The complete ORIGINAL R1--R3 raw rectangle structure on the
actual vertex direct limit, not just on its effective G-reduct. -/
noncomputable def limitRawPresentation
    (T : FiniteRawActionPairTower d V) :
    RawRectanglePresentation d T.VertexLimit where
  part := T.limitPart
  part_equiv := T.limitPart_equivalence
  colour := T.limitColour
  colour_none_iff := T.limitColour_none_iff
  colour_reverse := T.limitColour_reverse
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁
      h₀₀ h₀₁ h₁₀ h₁₁
    obtain ⟨n, a, b, c, e, ha, hb, hc, he⟩ :=
      T.exists_four_at_sameStage x₀ x₁ y₀ y₁
    subst x₀
    subst x₁
    subst y₀
    subst y₁
    have hx' : (T.stage n).raw.part a b :=
      (T.limitPart_of n a b).mp hx
    have hy' : (T.stage n).raw.part c e :=
      (T.limitPart_of n c e).mp hy
    rw [T.limitColour_of] at h₀₀ h₀₁ h₁₀ h₁₁
    exact (T.stage n).raw.rectangle a b c e hx' hy'
      c₀₀ c₀₁ c₁₀ c₁₁ h₀₀ h₀₁ h₁₀ h₁₁

/-- Each canonical finite-stage inclusion is induced also for
the newly assembled complete raw rectangle, preserving and reflecting
E and ALL ordered original raw colours. -/
theorem limitRawPresentation_part_iff
    (T : FiniteRawActionPairTower d V)
    (n : ℕ) (x y : V n) :
    T.limitRawPresentation.part (T.vertexOf n x) (T.vertexOf n y) ↔
      (T.stage n).raw.part x y :=
  T.limitPart_of n x y

theorem limitRawPresentation_colour_eq
    (T : FiniteRawActionPairTower d V)
    (n : ℕ) (x y : V n) :
    T.limitRawPresentation.colour (T.vertexOf n x) (T.vertexOf n y) =
      (T.stage n).raw.colour x y :=
  T.limitColour_of n x y

end FiniteRawActionPairTower
end SemigenericEPPA
