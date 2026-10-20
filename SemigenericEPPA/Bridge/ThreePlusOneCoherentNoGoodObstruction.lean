import SemigenericEPPA.Bridge.ThreePlusOneTypedTransposition
import SemigenericEPPA.Bridge.NoGoodColourInvolutionProfile
import SemigenericEPPA.Bridge.TypedRawEffectiveColourEmbedding
import SemigenericEPPA.Bridge.CoherentClosedSubsetInvolution
import SemigenericEPPA.Bridge.TypedRawAutomorphismPermutation

/-!
# Coherence on one actual 3+1 raw old gadget forces S to be nonempty

Take arbitrary effective delta!=1 and raw old colours of the
three edges from the singleton old vertex v to the tripleton
E-part a,b,c, with effective profile delta,1,1.
The underlying four-vertex presentation and its exact typed
partial involution tau swapping a,b while fixing c are already
formally defined, with NO raw fixed-point condition on the
three chosen edge colours.

Any true upstream coherent EPPA witness of this old structure
has a whole-witness involution T extending tau. The typed
embedding preserves the three effective old edge colours
literally, and the witness automorphism preserves all raw
predicates. The geometric 3+1 profile lemma then forces an
actual raw self-reversing colour somewhere in the witness.

Thus no-good-colour data with G!=1 cannot have coherent EPPA.
No finiteness or size bound on the witness is used in this
obstruction; witnesses may vary across old structures.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}

/-- Any typed coherent witness of the actual 3+1 old rectangle
profile delta,1,1 forces a genuine self-reversing raw colour. -/
theorem RawDatum.goodNonempty_of_threePlusOneCoherentWitness
    (d : RawDatum G C)
    (col : Option Bool → C)
    (delta : G) (hne : delta ≠ 1)
    (hcolA : d.phi (col none) = delta)
    (hcolB : d.phi (col (some false)) = 1)
    (hcolC : d.phi (col (some true)) = 1)
    (W : Type w)
    (Q : RawRectanglePresentation d W)
    (ψ : Structure.Embedding (rectangleTrivialAction C)
      (d.threePlusOneRawPresentation col).toStructure
      Q.toStructure)
    (hwitness : Structure.IsCoherentEPPAWitness
      (rectangleTrivialAction C) ψ) :
    d.selfReverseEffective.Nonempty := by
  classical
  let P := d.threePlusOneRawPresentation col
  let p := d.threePlusOneTypedTransposition col
  obtain ⟨e⟩ := hwitness
  obtain ⟨hsrc, htgt, hlang, hsq⟩ :=
    d.threePlusOneTypedTransposition_exactSquare col
  have hclosed : P.toStructure.IsClosed threePlusOneSwapSource := by
    intro n F xs hx
    exact PEmpty.elim F
  let T : Structure.Automorphism
      (rectangleTrivialAction C) Q.toStructure := e.extension p
  have hT2 (x : W) : T (T x) = x :=
    coherentExtension_involution_of_squareOnSource
      (rectangleTrivialAction C) e p threePlusOneSwapSource
      hclosed hsrc htgt hlang hsq x
  let perm : Equiv.Perm W := Q.typedAutomorphismPerm T
  have hperm2 (x : W) : perm (perm x) = x := hT2 x
  have hψPart (x y : Option (Option Bool)) :
      Q.part (ψ x) (ψ y) ↔ P.part x y := by
    have hlangψ : ψ.lang = (1 : Equiv.Perm (Fin 0)) := by
      apply Equiv.ext
      intro i
      exact Fin.elim0 i
    have h := ψ.map_rel_iff
      (binarySymbol C none) (pairTuple x y)
    rw [hlangψ, Language.Action.onRel_one] at h
    change Q.part (ψ x) (ψ y) ↔ P.part x y at h
    exact h
  have ha : (some none : Option (Option Bool)) ∈
      threePlusOneSwapSource := by
    simp [threePlusOneSwapSource]
  have hb : (some (some false) : Option (Option Bool)) ∈
      threePlusOneSwapSource := by
    simp [threePlusOneSwapSource]
  have hc : (some (some true) : Option (Option Bool)) ∈
      threePlusOneSwapSource := by
    simp [threePlusOneSwapSource]
  have hTa : perm (ψ (some none)) = ψ (some (some false)) := by
    have h := (e.extension_spec p).2 (some none) (hsrc.symm ▸ ha)
    change T (ψ (some none)) = ψ (p (some none)) at h
    have hp : p (some none) = some (some false) := rfl
    rw [hp] at h
    exact h
  have hTb :
      perm (ψ (some (some false))) = ψ (some none) := by
    have h := (e.extension_spec p).2
      (some (some false)) (hsrc.symm ▸ hb)
    change T (ψ (some (some false))) =
      ψ (p (some (some false))) at h
    have hp : p (some (some false)) = some none := rfl
    rw [hp] at h
    exact h
  have hTc :
      perm (ψ (some (some true))) = ψ (some (some true)) := by
    have h := (e.extension_spec p).2
      (some (some true)) (hsrc.symm ▸ hc)
    change T (ψ (some (some true))) =
      ψ (p (some (some true))) at h
    have hp : p (some (some true)) = some (some true) := rfl
    rw [hp] at h
    exact h
  have hab : Q.part (ψ (some none))
      (ψ (some (some false))) :=
    (hψPart _ _).mpr (d.threePlusOne_part_ab col)
  have hac : Q.part (ψ (some none))
      (ψ (some (some true))) :=
    (hψPart _ _).mpr (d.threePlusOne_part_ac col)
  have hva : ¬Q.part (ψ none) (ψ (some none)) := by
    intro h
    exact d.threePlusOne_cross_va col ((hψPart _ _).mp h)
  have hvalA :
      Q.effectiveReduct.F (ψ none) (ψ (some none)) = delta := by
    calc
      Q.effectiveReduct.F (ψ none) (ψ (some none)) =
          P.effectiveReduct.F none (some none) :=
        P.effectiveColour_of_typedEmbedding Q ψ none (some none)
          (d.threePlusOne_cross_va col)
      _ = d.phi (col none) := d.threePlusOne_effective_va col
      _ = delta := hcolA
  have hvalB :
      Q.effectiveReduct.F (ψ none) (ψ (some (some false))) = 1 := by
    have hcross : ¬P.part none (some (some false)) := by
      simp [P, RawDatum.threePlusOneRawPresentation]
    calc
      Q.effectiveReduct.F (ψ none) (ψ (some (some false))) =
          P.effectiveReduct.F none (some (some false)) :=
        P.effectiveColour_of_typedEmbedding Q ψ none
          (some (some false)) hcross
      _ = d.phi (col (some false)) :=
        d.threePlusOne_effective_vb col
      _ = 1 := hcolB
  have hvalC :
      Q.effectiveReduct.F (ψ none) (ψ (some (some true))) = 1 := by
    have hcross : ¬P.part none (some (some true)) := by
      simp [P, RawDatum.threePlusOneRawPresentation]
    calc
      Q.effectiveReduct.F (ψ none) (ψ (some (some true))) =
          P.effectiveReduct.F none (some (some true)) :=
        P.effectiveColour_of_typedEmbedding Q ψ none
          (some (some true)) hcross
      _ = d.phi (col (some true)) :=
        d.threePlusOne_effective_vc col
      _ = 1 := hcolC
  exact Q.goodNonempty_of_threePointProfileInvolution
    perm (Q.typedAutomorphismPerm_colour T) hperm2
    (ψ (some none)) (ψ (some (some false)))
    (ψ (some (some true))) (ψ none)
    hab hac hva hTa hTb hTc
    delta hne hvalA hvalB hvalC

/-- If G has a nontrivial element and ALL actual 3+1 gadgets
have a typed coherent witness, then the good effective colour
set is nonempty. The witness may depend on the old gadget,
as in the EPPA property; no common bound is assumed. -/
theorem RawDatum.goodNonempty_of_threePlusOneCoherentWitnesses
    (d : RawDatum G C)
    (delta : G) (hne : delta ≠ 1)
    (hwitness : ∀ (col : Option Bool → C),
      ∃ (W : Type w)
        (Q : RawRectanglePresentation d W)
        (ψ : Structure.Embedding (rectangleTrivialAction C)
          (d.threePlusOneRawPresentation col).toStructure
          Q.toStructure),
        Structure.IsCoherentEPPAWitness
          (rectangleTrivialAction C) ψ) :
    d.selfReverseEffective.Nonempty := by
  obtain ⟨cDelta, hcDelta⟩ := d.phi_surjective delta
  obtain ⟨cOne, hcOne⟩ := d.phi_surjective 1
  let col : Option Bool → C := fun i =>
    match i with
    | none => cDelta
    | some _ => cOne
  obtain ⟨W, Q, ψ, hcoh⟩ := hwitness col
  apply d.goodNonempty_of_threePlusOneCoherentWitness
    col delta hne (by simpa [col] using hcDelta)
    (by simpa [col] using hcOne)
    (by simpa [col] using hcOne) W Q ψ hcoh

end SemigenericEPPA
