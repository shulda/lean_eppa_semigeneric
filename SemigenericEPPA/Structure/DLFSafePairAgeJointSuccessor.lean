import SemigenericEPPA.Structure.DisjointRawJointEmbedding
import SemigenericEPPA.Structure.DLFSafePairOverAgeExtension

/-!
# One finite safe-pair successor can also contain any prescribed finite age member

The crucial relative finite semi-coherent EPPA theorem already
allows an old safe pair (A,H) to sit inside an arbitrary larger
finite raw presentation P, with no H-action required on the new
vertices. To force age cofinality, use the unconditional original
raw disjoint-union JEP to place any prescribed finite raw Q beside A,
then invoke that relative theorem.

The output is ONE finite genuine safe pair (B,K), a strict induced
and equivariant safe-pair embedding (A,H)→(B,K), and an independent
induced raw embedding Q→B. Both are in the exact E/R_c language.

This is a finite successor with an arbitrary prescribed age target,
not yet a countable cofinal tower. JEP, not unrestricted finite SAP,
is sufficient for this particular step.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {V : Type w} [Fintype V]
variable {W : Type t} [Fintype W]
variable {d : RawDatum G C}

namespace FiniteSafeRawPair

/-- Positive age-target extension: every finite safe original raw pair
can be enlarged while preserving its ACTUAL subgroup action, and
simultaneously containing a genuine induced copy of ANY finite original
raw rectangle, using only one complete good affine orbit.

The target's original E and ordered raw colours are preserved
and reflected exactly. -/
theorem exists_safeExtension_containingFiniteRaw
    (A : FiniteSafeRawPair d V)
    (Q : RawRectanglePresentation d W)
    (hOrbit : d.HasCompleteGoodOrbit) :
    ∃ (Z : Type (max u (max v (max (max w t) w))))
      (hZ : Finite Z),
      letI : Finite Z := hZ
      ∃ (B : FiniteSafeRawPair d Z)
        (f : FiniteSafeRawPairEmbedding A B)
        (q : W → Z),
        Function.Injective q ∧
        (∀ x y : W, B.raw.part (q x) (q y) ↔ Q.part x y) ∧
        (∀ x y : W, B.raw.colour (q x) (q y) = Q.colour x y) := by
  classical
  let c : C := Classical.choose (d.phi_surjective 1)
  let R : RawRectanglePresentation d (V ⊕ W) :=
    A.raw.disjointJoint Q c
  have hInj : Function.Injective (Sum.inl : V → V ⊕ W) := by
    intro x y h
    exact Sum.inl.inj h
  have hPart : ∀ x y : V,
      R.part (Sum.inl x) (Sum.inl y) ↔ A.raw.part x y := by
    intro x y
    exact Iff.rfl
  have hColour : ∀ x y : V,
      R.colour (Sum.inl x) (Sum.inl y) =
        A.raw.colour x y := by
    intro x y
    rfl
  obtain ⟨Z, hZ, B, f, eR, hEInj, hEPart, hEColour,
      _hOld, _hPartials⟩ :=
    A.exists_safeExtension_overRawEmbedding
      R Sum.inl hInj hPart hColour hOrbit
  letI : Finite Z := hZ
  refine ⟨Z, hZ, B, f, (fun x : W => eR (Sum.inr x)),
    ?_, ?_, ?_⟩
  · intro x y hxy
    apply Sum.inr.inj
    exact hEInj hxy
  · intro x y
    exact (hEPart (Sum.inr x) (Sum.inr y)).trans Iff.rfl
  · intro x y
    exact (hEColour (Sum.inr x) (Sum.inr y)).trans rfl

end FiniteSafeRawPair
end SemigenericEPPA
