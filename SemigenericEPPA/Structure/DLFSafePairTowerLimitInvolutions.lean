import SemigenericEPPA.Structure.DLFSafePairTowerDirectedLimits

/-!
# A group-colimit involution already comes from a genuine finite-stage involution

The DLF negative and safety arguments may inspect square-one elements
of the true algebraic direct limit of finite acting automorphism
groups. Injectivity of every canonical old-group inclusion guarantees
that the order-two condition is reflected back to a finite stage,
rather than being created by identifications in the quotient.

This is an exact statement about the concrete group direct limit,
not an abstract finite-group parity replacement.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- Every square-one element of the genuine group colimit has a
square-one representative in one actual finite safe subgroup. -/
theorem groupLimit_squareOne_has_finiteRepresentative
    (T : FiniteSafeRawPairTower d V)
    (g : T.GroupLimit) (hg : g * g = 1) :
    ∃ (n : ℕ) (h : (T.stage n).subgroup),
      g = T.groupOf n h ∧ h * h = 1 := by
  obtain ⟨n, h, hh⟩ :=
    DirectLimit.exists_eq_mk (f := T.groupTransition) g
  have hProd : T.groupOf n h * T.groupOf n h =
      T.groupOf n (h * h) := by
    change (⟦⟨n, h⟩⟧ : T.GroupLimit) * ⟦⟨n, h⟩⟧ =
      ⟦⟨n, h * h⟩⟧
    exact DirectLimit.mul_def (f := T.groupTransition) n h h
  have hOne : (1 : T.GroupLimit) = T.groupOf n 1 :=
    DirectLimit.one_def (f := T.groupTransition) n
  have hEq : T.groupOf n (h * h) =
      T.groupOf n (1 : (T.stage n).subgroup) := by
    calc
      T.groupOf n (h * h) = T.groupOf n h * T.groupOf n h := hProd.symm
      _ = g * g := by rw [← hh]
      _ = 1 := hg
      _ = T.groupOf n 1 := hOne
  have hSquare : h * h = 1 :=
    T.groupOf_injective n hEq
  exact ⟨n, h, hh, hSquare⟩

end FiniteSafeRawPairTower
end SemigenericEPPA
