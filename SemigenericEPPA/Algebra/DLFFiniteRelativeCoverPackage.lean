import SemigenericEPPA.Algebra.DLFRelativeCoverSurjectiveSplit
import SemigenericEPPA.Algebra.DLFChainSemidirectFinite

/-!
# The full finite split relative group cover, with no bad involutive lifts

Combines the exact SAME prescribed-boundary subgroup of the finite
F₂-chain semidirect group with:
* finite carrier;
* a strict surjective group homomorphism onto Q;
* an injective strict homomorphic section of H≤Q;
* all upstairs square-one elements project to conjugates of H,
  unless their projection is trivial (which is already in H).

This is the complete algebraic relative involution-killing cover
needed for the positive DLF construction. No faithful action on
an R1--R3 structure or relative safe EPPA is claimed here.

The subgroup H need not be normal and the group Q may be
nonabelian. All assertions concern the one fixed relative graph
and the same basepoint identity coset, with no fresh group choices.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u
variable {Q : Type u} [Group Q]

/-- The canonical relative finite cover satisfies the complete
algebraic extension and involution-control requirements.
Every square-one element has projection conjugate into H.
This includes the possible square-one identity element. -/
theorem finite_relativeCover_allProperties
    (H : Subgroup Q) [Finite Q]
    [Fintype (CoverVertex H)] [LinearOrder (CoverVertex H)]
    [Fintype (CoverEdge H)] [LinearOrder (CoverEdge H)] :
    Finite (relativeBoundaryCover H) ∧
      Function.Surjective (relativeCoverProjection H) ∧
      Function.Injective (relativeCoverSection H) ∧
      (∀ h : H,
        relativeCoverProjection H (relativeCoverSection H h) = h.val) ∧
      (∀ a : relativeBoundaryCover H,
        a * a = 1 →
          ∃ q : Q,
            q⁻¹ * relativeCoverProjection H a * q ∈ H) := by
  classical
  refine ⟨inferInstance,
    relativeCoverProjection_surjective H,
    relativeCoverSection_injective H,
    relativeCoverProjection_section H, ?_⟩
  intro a ha
  by_contra hbad
  have hNoConjugate : ∀ q : Q, q⁻¹ * a.val.base * q ∉ H := by
    intro q hq
    apply hbad
    exact ⟨q, hq⟩
  have haSq : a.val * a.val = 1 := by
    exact congrArg Subtype.val ha
  exact relativeBoundaryCover_noBadInvolutiveLift
    H a haSq hNoConjugate

end RelativeDLF
end SemigenericEPPA
