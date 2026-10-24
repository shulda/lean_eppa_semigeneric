import SemigenericEPPA.Structure.DLFSafePairTowerLimitRawData

/-!
# E-equivalence and literal raw reversal on the DLF vertex limit

The actual vertex direct limit has E and Option C-colour functions
defined by quotient elimination. The finite original-language
R1--R3 axioms now transport to the limit, using common-stage
representatives for finitely many quotient vertices:

* E is reflexive, symmetric, transitive;
* a pair has raw colour none exactly when it lies in E;
* all ordered colours reverse exactly under d.reverse.

The remaining four-point rectangle equation will be handled
independently before assembling the infinite raw presentation.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- E on the actual vertex colimit is a genuine equivalence
relation, not merely reflexive up to representatives. -/
theorem limitPart_equivalence (T : FiniteSafeRawPairTower d V) :
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
      ((T.stage i).raw.part_equiv.symm a b ((T.limitPart_of i a b).1 hab))
  · intro x y z
    refine DirectLimit.induction₃ (f := T.vertexTransition) ?_ x y z
    intro i a b c
    change T.limitPart (T.vertexOf i a) (T.vertexOf i b) →
      T.limitPart (T.vertexOf i b) (T.vertexOf i c) →
      T.limitPart (T.vertexOf i a) (T.vertexOf i c)
    intro hab hbc
    exact (T.limitPart_of i a c).2
      ((T.stage i).raw.part_equiv.trans a b c
        ((T.limitPart_of i a b).1 hab)
        ((T.limitPart_of i b c).1 hbc))

/-- Complete literal raw-colour support is precisely the complement
of E, in the actual quotient direct-limit structure. -/
theorem limitColour_none_iff (T : FiniteSafeRawPairTower d V)
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
theorem limitColour_reverse (T : FiniteSafeRawPairTower d V)
    (x y : T.VertexLimit) :
    T.limitColour y x =
      Option.map d.reverse (T.limitColour x y) := by
  refine DirectLimit.induction₂ (f := T.vertexTransition) ?_ x y
  intro i a b
  change T.limitColour (T.vertexOf i b) (T.vertexOf i a) =
    Option.map d.reverse (T.limitColour (T.vertexOf i a) (T.vertexOf i b))
  rw [T.limitColour_of, T.limitColour_of]
  exact (T.stage i).raw.colour_reverse a b

end FiniteSafeRawPairTower
end SemigenericEPPA
