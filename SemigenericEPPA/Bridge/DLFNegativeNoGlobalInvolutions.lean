import SemigenericEPPA.Bridge.DLFNegativeCrossInvolutionOrbitForcing
import SemigenericEPPA.Structure.DLFNegativeRelativeRowMultiplier
import SemigenericEPPA.Bridge.DLFNegativeNoWithinPartInvolution

/-!
# No involutions in the nontrivial-G / no-complete-good-orbit full-age limit

The two independent negative DLF geometric obstructions combine
without any finite subgroup or "safe pair" assumption.

(1) A raw order-two automorphism T with a cross-E swapped pair
forces a complete good congruence orbit. A three-vertex raw
relative extension over that particular pair realizes every
group multiplier. Hence no cross-E swaps are possible when the
complete-good-orbit hypothesis fails.

(2) A within-E swapped pair produces a third same-part vertex
and a fresh singleton with an asymmetric delta row, forcing
ANOTHER cross-E swapped pair, contradiction.

Therefore EVERY raw-colour-preserving order-two permutation of
the homogeneous original R1--R3 limit is IDENTICAL. The
homogeneous full-age hypotheses are explicitly separated by
universe: small three-vertex extensions and arbitrary finite
substructure profiles. Both are available in the complete
Fraisse age; the final DLF iff API still needs to package that
universe normalization together with an actual two-cycle.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Nontrivial G]
variable {C : Type v} {V : Type w}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- For a nontrivial effective group with NO complete good orbit,
any genuine involutive permutation preserving every original
ordered raw colour is the identity, assuming exact full finite
age and original-language partial-map homogeneity. -/
theorem involutiveRawAutomorphism_eq_one_of_noCompleteGoodOrbit
    (M : RawRectanglePresentation d V)
    (hNoOrbit : ¬d.HasCompleteGoodOrbit)
    (hAgeSmall : ∀ (W : Type) [Fintype W]
      (Q : RawRectanglePresentation d W),
      ∃ t : W → V,
        Function.Injective t ∧
        (∀ x y : W, M.part (t x) (t y) ↔ Q.part x y) ∧
        (∀ x y : W, M.colour (t x) (t y) = Q.colour x y))
    (hAge : ∀ (W : Type w) [Fintype W]
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
        ∀ x : K, α.val x.val = p x)
    (T : Equiv.Perm V)
    (hTcolour : ∀ x y : V, M.colour (T x) (T y) = M.colour x y)
    (hTtwo : ∀ z : V, T (T z) = z) :
    T = 1 := by
  classical
  have hNoCross (x y : V) (hxy : ¬M.part x y)
      (hTx : T x = y) (hTy : T y = x) : False := by
    have hRows :=
      M.leftMultiplierRows_of_fullAge_homogeneous
        hAgeSmall hHom x y hxy
    exact M.no_crossInvolution_of_noCompleteGoodOrbit_and_rows
      hNoOrbit T hTcolour hTtwo x y hxy hTx hTy hRows
  apply Equiv.ext
  intro b
  by_contra hMove
  by_cases hSame : M.part b (T b)
  · exact M.no_withinPartInvolution_swap_of_noCrossSwap
      hAge hHom T hTcolour hTtwo hNoCross
      (T b) b (M.part_equiv.symm hSame) hMove rfl
  · exact hNoCross b (T b) hSame rfl (hTtwo b)

end RawRectanglePresentation
end SemigenericEPPA
