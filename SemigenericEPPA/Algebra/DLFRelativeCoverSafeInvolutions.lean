import SemigenericEPPA.Algebra.DLFSafeConjugateInvolution
import SemigenericEPPA.Algebra.DLFFiniteRelativeCoverPackage

/-!
# A finite split relative cover preserves EVERY safe H-involution orbit

Let H≤Q and let Q act by exact E/F automorphisms of one finite
effective geometry D. Suppose H is locally safe: whenever one of its
involutions exchanges an actual cross-E pair, the full affine
congruence orbit of the pair's effective colour contains only good
raw-colour fibres.

The relative cover \widetilde{Q}→Q is surjective with a strict H
section and kills ALL involutions whose images are not conjugate
into H. Every surviving involution has its projection conjugate
to an element of H. The independently certified conjugacy
transport lemma then proves that its exchanged effective cross
pairs are locally safe, WITHOUT global good-set saturation.

This is the algebraic safety premise needed after realizing the
relative cover group faithfully by one additional raw E-class.
It does not yet construct the relative safe EPPA witness A≤B.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v w t
variable {Q : Type u} [Group Q]
variable {G : Type v} [Group G]
variable {C : Type w} {V : Type t}
variable {d : RawDatum G C}

/-- The fixed relative cover acts on the old geometry through
its canonical projection to Q, with no independent action choices. -/
noncomputable def relativeCoverOldAction
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [LinearOrder (CoverVertex H)]
    [Fintype (CoverEdge H)] [LinearOrder (CoverEdge H)]
    (rho : Q →* Equiv.Perm V) :
    relativeBoundaryCover H →* Equiv.Perm V :=
  rho.comp (relativeCoverProjection H)

/-- For ANY actual involution in the finite relative cover,
its old-geometry swapped E-cross-pairs have an entire good
congruence orbit as long as the prescribed H-involutions do.
There are no extra saturation assumptions on other effective
colours. -/
theorem relativeCover_involutions_preserve_safeOrbits
    (H : Subgroup Q)
    [Finite Q]
    [Fintype (CoverVertex H)] [LinearOrder (CoverVertex H)]
    [Fintype (CoverEdge H)] [LinearOrder (CoverEdge H)]
    (D : EffectiveGeometry d.s V)
    (rho : Q →* Equiv.Perm V)
    (hE : ∀ (q : Q) (x y : V),
      D.part (rho q x) (rho q y) ↔ D.part x y)
    (hF : ∀ (q : Q) (x y : V),
      ¬D.part x y → D.F (rho q x) (rho q y) = D.F x y)
    (hSafeH : ∀ (h : H), h * h = 1 →
      ∀ (x y : V), ¬D.part x y →
        rho h.val x = y → rho h.val y = x →
          d.GoodCompleteOrbitAt (D.F x y)) :
    ∀ (a : relativeBoundaryCover H), a * a = 1 →
      ∀ (x y : V), ¬D.part x y →
        relativeCoverOldAction H rho a x = y →
        relativeCoverOldAction H rho a y = x →
          d.GoodCompleteOrbitAt (D.F x y) := by
  obtain ⟨_hFinite, _hSurj, _hInject, _hSplit, hConj⟩ :=
    finite_relativeCover_allProperties H
  intro a htwo x y hxy hax hay
  obtain ⟨q, hq⟩ := hConj a htwo
  let h : H := ⟨q⁻¹ * relativeCoverProjection H a * q, hq⟩
  have ht : relativeCoverProjection H a =
      q * h.val * q⁻¹ := by
    dsimp [h]
    group
  have htSq : relativeCoverProjection H a *
      relativeCoverProjection H a = 1 := by
    have hh := congrArg (relativeCoverProjection H) htwo
    simpa only [map_mul, map_one] using hh
  change rho (relativeCoverProjection H a) x = y at hax
  change rho (relativeCoverProjection H a) y = x at hay
  exact d.goodCompleteOrbitAt_conjugate_involution
    D rho hE hF H hSafeH
    (relativeCoverProjection H a) q h
    htSq ht x y hxy hax hay

end RelativeDLF
end SemigenericEPPA
