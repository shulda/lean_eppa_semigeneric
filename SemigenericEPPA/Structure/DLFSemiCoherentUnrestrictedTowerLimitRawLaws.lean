import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitRawData

/-!
# Unrestricted semi-coherent action-tower colimit: LimitRawLaws

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

/-- E on the actual vertex colimit is a genuine equivalence
relation, not merely reflexive up to representatives. -/
theorem limitPart_equivalence (T : FiniteRawActionPairTower d V) :
    Equivalence T.limitPart := by
  constructor
  · intro x
    refine DirectLimit.induction (f := T.vertexTransition) ?_ x
    intro i a
    change T.limitPart (T.vertexOf i a) (T.vertexOf i a)
    exact (T.limitPart_of i a a).2 ((T.stage i).raw.part_equiv.refl a)
  · intro x y
    refine DirectLimit.induction₂ (f := T.vertexTransition) ?_ x y
    intro i a b
    change T.limitPart (T.vertexOf i a) (T.vertexOf i b) →
      T.limitPart (T.vertexOf i b) (T.vertexOf i a)
    intro hab
    exact (T.limitPart_of i b a).2
      ((T.stage i).raw.part_equiv.symm ((T.limitPart_of i a b).1 hab))
  · intro x y z
    refine DirectLimit.induction₃ (f := T.vertexTransition) ?_ x y z
    intro i a b c
    change T.limitPart (T.vertexOf i a) (T.vertexOf i b) →
      T.limitPart (T.vertexOf i b) (T.vertexOf i c) →
      T.limitPart (T.vertexOf i a) (T.vertexOf i c)
    intro hab hbc
    exact (T.limitPart_of i a c).2
      ((T.stage i).raw.part_equiv.trans
        ((T.limitPart_of i a b).1 hab)
        ((T.limitPart_of i b c).1 hbc))

/-- Complete literal raw-colour support is precisely the complement
of E, in the actual quotient direct-limit structure. -/
theorem limitColour_none_iff (T : FiniteRawActionPairTower d V)
    (x y : T.VertexLimit) :
    T.limitColour x y = none ↔ T.limitPart x y := by
  refine DirectLimit.induction₂ (f := T.vertexTransition) ?_ x y
  intro i a b
  change T.limitColour (T.vertexOf i a) (T.vertexOf i b) = none ↔
    T.limitPart (T.vertexOf i a) (T.vertexOf i b)
  rw [T.limitColour_of, T.limitPart_of]
  exact (T.stage i).raw.colour_none_iff a b

/-- Ordered raw colours reverse exactly in the ORIGINAL alphabet C
on the vertex quotient limit. No effective-colour shortcuts. -/
theorem limitColour_reverse (T : FiniteRawActionPairTower d V)
    (x y : T.VertexLimit) :
    T.limitColour y x =
      Option.map d.reverse (T.limitColour x y) := by
  refine DirectLimit.induction₂ (f := T.vertexTransition) ?_ x y
  intro i a b
  change T.limitColour (T.vertexOf i b) (T.vertexOf i a) =
    Option.map d.reverse (T.limitColour (T.vertexOf i a) (T.vertexOf i b))
  rw [T.limitColour_of, T.limitColour_of]
  exact (T.stage i).raw.colour_reverse a b

end FiniteRawActionPairTower
end SemigenericEPPA
