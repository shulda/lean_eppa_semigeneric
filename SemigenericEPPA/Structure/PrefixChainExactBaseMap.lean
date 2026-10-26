import SemigenericEPPA.Structure.FinitePrefixOnePointChain
import SemigenericEPPA.Structure.FiniteChainExactBaseMap

/-!
# The specified finite-prefix chain has the specified old embedding

The canonical finite one-point prefix chain from X ⊕ Fin m
does not merely include an isomorphic copy of the initial
X ⊕ Fin 0. The composite old-vertex embedding from prefix
zero to prefix n agrees LITERALLY, after the actual n-prefix
inclusion, with the given inclusion into X ⊕ Fin m.

This is an exact map-level coherence theorem needed to transport
the final canonical strong amalgamation square to the original
input span, rather than some independently chosen old copy.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}

/-- The true prescribed chain inclusion, represented inside
the full original R1--R3 vertex carrier, equals the direct
initial-prefix inclusion pointwise. -/
theorem finitePrefix_fromZero_toFinal
    {X : Type (max u v)} [Fintype X] {m : ℕ}
    (P : Structure (rectangleLanguage C) (X ⊕ Fin m))
    (hP : IsRectangleStructure d P) :
    ∀ (n : ℕ) (hn : n ≤ m) (x : PrefixCarrier X m 0),
      prefixToFinal m n
        ((finitePrefixOnePointChain P hP).fromZero n hn x) =
      prefixToFinal m 0 x := by
  intro n
  induction n with
  | zero =>
      intro _hn x
      rfl
  | succ n ih =>
      intro hn x
      have hlt : n < m := Nat.lt_of_succ_le hn
      have hprev : n ≤ m := Nat.le_of_lt hlt
      change
        prefixToFinal m (n+1)
          (prefixStep m n hlt
            ((finitePrefixOnePointChain P hP).fromZero n hprev x)) =
        prefixToFinal m 0 x
      rw [prefixToFinal_step m n hlt]
      exact ih hprev x

end SemigenericEPPA
