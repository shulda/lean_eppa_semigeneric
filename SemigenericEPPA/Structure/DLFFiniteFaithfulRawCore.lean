import SemigenericEPPA.Structure.DLFFiniteInvariantRawAction
import SemigenericEPPA.Algebra.DLFFiniteFaithfulInvariantCarrier

/-!
# Actual finite faithful induced raw action core of any finite automorphism subgroup

The negative DLF argument begins with an actual FINITE subgroup
H of the automorphism group of an infinite original-language
R1–R3 structure M. We now construct a finite H-invariant vertex
set which separates EVERY pair of distinct H-elements.

The induced raw rectangle on this finite set is an actual
original E/R_c presentation, and H acts by a STRICT INJECTIVE
homomorphism into its permutation group, preserving E and all
ordered literal R_c predicates.

This is not a new abstract replacement for H, and it does not
assume that an arbitrary earlier finite set is invariant or
that old extensions preserve an external H-action.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Every finite actual subgroup H≤Aut_raw(M) admits one
literal finite induced original-language core on which its action
remains faithful and preserves every raw predicate. -/
theorem exists_finiteFaithfulInvariantRawCore
    (M : RawRectanglePresentation d V)
    (H : Subgroup (Equiv.Perm V))
    [Finite H]
    (hAut : H ≤ M.fullRawAutGroup) :
    ∃ F : Finset V,
      let S := {x : V // x ∈ F}
      ∃ rho : H →* Equiv.Perm S,
        Function.Injective rho ∧
        (∀ (h : H) (x y : S),
          (M.pullbackRaw Subtype.val).part
            (rho h x) (rho h y) ↔
              (M.pullbackRaw Subtype.val).part x y) ∧
        (∀ (h : H) (x y : S),
          (M.pullbackRaw Subtype.val).colour
            (rho h x) (rho h y) =
              (M.pullbackRaw Subtype.val).colour x y) := by
  classical
  obtain ⟨F, hInv, hSep⟩ :=
    finiteGroup_exists_finiteFaithfulInvariantCarrier H
  let rho : H →* Equiv.Perm {x : V // x ∈ F} :=
    finiteInvariantRawAction H F hInv
  refine ⟨F, rho, ?_, ?_, ?_⟩
  · exact finiteInvariantRawAction_injective H F hInv hSep
  · intro h x y
    exact M.finiteInvariantRawAction_part H hAut F hInv h x y
  · intro h x y
    exact M.finiteInvariantRawAction_colour H hAut F hInv h x y

end RawRectanglePresentation
end SemigenericEPPA
