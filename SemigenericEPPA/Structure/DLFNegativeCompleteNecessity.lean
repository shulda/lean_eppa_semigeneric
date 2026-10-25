import SemigenericEPPA.Bridge.DLFNegativeNoGlobalInvolutions
import SemigenericEPPA.Structure.DLFNegativeGlobalTwoCycle
import SemigenericEPPA.Structure.DLFNormalizeFiniteRawToFin
import SemigenericEPPA.Algebra.DLFDenseSwappedPairForcesInvolution

/-!
# Full negative DLF direction from the canonical finite raw age

For a NONTRIVIAL finite effective group G, a homogeneous
original-language raw R1–R3 structure containing every finite
raw rectangle on canonical carriers Fin n cannot admit a
dense locally finite subgroup of its ACTUAL raw automorphism
group unless there is a complete good affine orbit.

The geometric part is the independently formalized no-global-
involutions result. The finite canonical age suffices for its
two age hypotheses by the certified finite carrier normalization.

Full finite age plus ultrahomogeneity also gives a genuine raw
automorphism with a literal two-cycle (its global order is not
asserted to be two). The already certified density/local finiteness
parity theorem places some nontrivial true involution in ANY
dense locally finite subgroup; but the geometric no-involutions
result forbids it.

This is the mathematical negative DLF converse with all
hypotheses stated literally, not an abstract groupoid reformulation.
All submodules must individually and jointly pass Lean CI and
the allowed-axiom audit before this result is certified.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Nontrivial G]
variable {C : Type v} {V : Type w}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Full canonical original R1–R3 age, literal finite-partial
ultrahomogeneity, and no complete good orbit are incompatible
with ANY dense locally finite subgroup of Aut_raw(M). -/
theorem no_denseLocallyFinite_of_noCompleteGoodOrbit
    (M : RawRectanglePresentation d V)
    (hNoOrbit : ¬d.HasCompleteGoodOrbit)
    (hFin : ∀ (n : ℕ) (Q : RawRectanglePresentation d (Fin n)),
      ∃ t : Fin n → V,
        Function.Injective t ∧
        (∀ x y : Fin n, M.part (t x) (t y) ↔ Q.part x y) ∧
        (∀ x y : Fin n, M.colour (t x) (t y) = Q.colour x y))
    (hHom : ∀ (K : Finset V) (p : K → V),
      Function.Injective p →
      (∀ x y : K, M.part (p x) (p y) ↔ M.part x.val y.val) →
      (∀ x y : K, M.colour (p x) (p y) = M.colour x.val y.val) →
      ∃ α : M.fullRawAutGroup,
        ∀ x : K, α.val x.val = p x) :
    ¬∃ L : Subgroup (Equiv.Perm V),
      L ≤ M.fullRawAutGroup ∧
      DenseByFiniteRestrictions M.fullRawAutGroup L ∧
      EveryFinitelyGeneratedSubgroupFinite L := by
  classical
  intro hDLF
  obtain ⟨L, hL, hDense, hLF⟩ := hDLF
  have hAgeSmall : ∀ (W : Type) [Fintype W]
      (Q : RawRectanglePresentation d W),
      ∃ t : W → V, Function.Injective t ∧
        (∀ x y : W, M.part (t x) (t y) ↔ Q.part x y) ∧
        (∀ x y : W, M.colour (t x) (t y) = Q.colour x y) :=
    M.inducedFiniteAge_of_canonicalFinAge hFin
  have hAge : ∀ (W : Type w) [Fintype W]
      (Q : RawRectanglePresentation d W),
      ∃ t : W → V, Function.Injective t ∧
        (∀ x y : W, M.part (t x) (t y) ↔ Q.part x y) ∧
        (∀ x y : W, M.colour (t x) (t y) = Q.colour x y) :=
    M.inducedFiniteAge_of_canonicalFinAge hFin
  have hNoInvol (T : Equiv.Perm V)
      (hTcolour : ∀ x y : V,
        M.colour (T x) (T y) = M.colour x y)
      (hTtwo : ∀ z : V, T (T z) = z) :
      T = 1 :=
    M.involutiveRawAutomorphism_eq_one_of_noCompleteGoodOrbit
      hNoOrbit hAgeSmall hAge hHom T hTcolour hTtwo
  obtain ⟨x, y, a, hxyNe, _hxyPart, hax, hay⟩ :=
    M.exists_fullRawAutomorphism_twoCycle_of_fullAge_homogeneous
      hAgeSmall hHom
  obtain ⟨t, htNe, htTwo⟩ :=
    denseLocallyFinite_has_nontrivial_involution_of_swappedPair
      M.fullRawAutGroup L hDense hLF a x y hax hay hxyNe
  let T : Equiv.Perm V := t.val
  let aT : M.fullRawAutGroup := ⟨t.val, hL t.property⟩
  have hTcolour : ∀ x y : V,
      M.colour (T x) (T y) = M.colour x y :=
    M.fullRawAutGroup_colour aT
  have hTSquare : (t.val * t.val : Equiv.Perm V) = 1 :=
    congrArg Subtype.val htTwo
  have hTtwo (z : V) : T (T z) = z := by
    have h := congrArg (fun p : Equiv.Perm V => p z) hTSquare
    simpa only [T, Equiv.Perm.mul_apply, one_apply] using h
  have hTOne : T = 1 := hNoInvol T hTcolour hTtwo
  have htOne : t = 1 := Subtype.ext hTOne
  exact htNe htOne

/-- Necessity of ONE complete good affine orbit for DLF in the
nontrivial effective-group case, under the genuine homogeneous
full-age hypotheses in the original E/R_c language. -/
theorem completeGoodOrbit_of_denseLocallyFinite
    (M : RawRectanglePresentation d V)
    (hFin : ∀ (n : ℕ) (Q : RawRectanglePresentation d (Fin n)),
      ∃ t : Fin n → V,
        Function.Injective t ∧
        (∀ x y : Fin n, M.part (t x) (t y) ↔ Q.part x y) ∧
        (∀ x y : Fin n, M.colour (t x) (t y) = Q.colour x y))
    (hHom : ∀ (K : Finset V) (p : K → V),
      Function.Injective p →
      (∀ x y : K, M.part (p x) (p y) ↔ M.part x.val y.val) →
      (∀ x y : K, M.colour (p x) (p y) = M.colour x.val y.val) →
      ∃ α : M.fullRawAutGroup,
        ∀ x : K, α.val x.val = p x)
    (hDLF : ∃ L : Subgroup (Equiv.Perm V),
      L ≤ M.fullRawAutGroup ∧
      DenseByFiniteRestrictions M.fullRawAutGroup L ∧
      EveryFinitelyGeneratedSubgroupFinite L) :
    d.HasCompleteGoodOrbit := by
  by_contra hNoOrbit
  exact (M.no_denseLocallyFinite_of_noCompleteGoodOrbit
    hNoOrbit hFin hHom) hDLF

end RawRectanglePresentation
end SemigenericEPPA
