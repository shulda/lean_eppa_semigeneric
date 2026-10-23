import SemigenericEPPA.Algebra.DLFFiniteRelativeCoverPackage
import SemigenericEPPA.Structure.ConstantNewPartProjectedCoverAutGroup

/-!
# The finite relative cover as a faithful action on a genuine R1--R3 structure

Fix finite Q with subgroup H and ANY genuine Q-action on an old
raw rectangle presentation P. The certified relative F₂-chain
group cover T has a surjective homomorphism π:T→Q and a split copy
H→T; every upstairs square-one element has base projection
conjugate into H.

We add one new E-class with carrier T and constant raw cross-colours.
On old vertices T acts via π followed by the given Q action;
on the new part T acts regularly. This makes the new action
faithful regardless of π's kernel, preserving E and all raw
R_c predicates on one exact finite R1--R3 presentation.

All constructions use the same T, π and H section. This is the
group-realisation ingredient for the DLF cofinal safe-pair
argument; the relative safe-group EPPA construction and the
cofinality/limit theorem are independent remaining gates.
-/

namespace SemigenericEPPA

universe u v w
variable {Q : Type u} [Group Q] [Finite Q]
variable {G : Type v} [Group G] {C : Type w}
variable {V : Type w}
variable {d : RawDatum G C}

namespace RelativeDLF

/-- Every abstract finite relative group cover with its split H
can be faithfully realised over any old raw Q-action by adjoining
one constant-coloured regular E-class. The section acts on old
points exactly as the original H restriction.

The final clause controls all involutions in this SAME realised
group: every order-two element projects to a conjugate of H. -/
theorem exists_faithfulRawRelativeCoverAction
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [LinearOrder (CoverVertex H)]
    [Fintype (CoverEdge H)] [LinearOrder (CoverEdge H)]
    (P : RawRectanglePresentation d V)
    (c0 : C)
    (rho : Q →* Equiv.Perm V)
    (hPart : ∀ (q : Q) (x y : V),
      P.part (rho q x) (rho q y) ↔ P.part x y)
    (hColour : ∀ (q : Q) (x y : V),
      P.colour (rho q x) (rho q y) = P.colour x y) :
    ∃ lift : relativeBoundaryCover H →* binaryRawAutSubgroup
        (fun x y : V ⊕ relativeBoundaryCover H =>
          (P.adjoinConstantNewPart
            (R := relativeBoundaryCover H) c0).part x y)
        (fun c x y =>
          (P.adjoinConstantNewPart
            (R := relativeBoundaryCover H) c0).colour x y = some c),
      Finite (relativeBoundaryCover H) ∧
      Function.Injective lift ∧
      Function.Surjective (relativeCoverProjection H) ∧
      Function.Injective (relativeCoverSection H) ∧
      (∀ (h : H) (x : V),
        (lift (relativeCoverSection H h)).val (.inl x) =
          .inl (rho h.val x)) ∧
      (∀ a : relativeBoundaryCover H, a * a = 1 →
        ∃ q : Q, q⁻¹ * relativeCoverProjection H a * q ∈ H) := by
  classical
  obtain ⟨hFinite, hSurjective, hSectionInj, _hSection,
    hNoBad⟩ := finite_relativeCover_allProperties H
  let π := relativeCoverProjection H
  let lift :=
    P.adjoinCoverGroupAutHom c0 rho π hPart hColour
  refine ⟨lift, hFinite, ?_, hSurjective, hSectionInj, ?_, hNoBad⟩
  · exact P.adjoinCoverGroupAutHom_injective c0 rho π hPart hColour
  · intro h x
    calc
      (lift (relativeCoverSection H h)).val (.inl x) =
          .inl (rho (π (relativeCoverSection H h)) x) :=
        P.adjoinCoverGroupAutHom_old c0 rho π
          hPart hColour (relativeCoverSection H h) x
      _ = .inl (rho h.val x) := by
        rw [relativeCoverProjection_section H h]

end RelativeDLF
end SemigenericEPPA
