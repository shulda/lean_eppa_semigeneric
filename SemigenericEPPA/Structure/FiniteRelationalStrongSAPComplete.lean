import SemigenericEPPA.Structure.OnePointAgainstCanonicalFiniteSAP
import SemigenericEPPA.Structure.CanonicalToRelativeOnePointSAP
import SemigenericEPPA.Structure.FiniteSAPExactSecondInduction
import SemigenericEPPA.Structure.FiniteRelationalStrongSAP
import SemigenericEPPA.Structure.FiniteExtensionNormalForm
import SemigenericEPPA.Structure.FinitePrefixBoundaryEquiv
import SemigenericEPPA.Structure.PullbackComposition

/-!
# Full finite strong amalgamation, in the original binary E/R_c language

Both input embeddings are arbitrary specified induced relational embeddings.
Normalize the LEFT finite extension over its actual base to X ⊕ Fin m,
then form its genuine finite one-point prefix chain. The canonical
one-point-vs-finite construction, after exact renaming, supplies the
local SAP hypothesis for the second induction. Finally transport the
resulting exact strong square back across the specified normalization,
preserving the input maps *literally*.

No coherence, DLF, involution-safety or Sági hypothesis is used.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v

variable {G : Type u} [Group G] {C : Type v}

namespace RawDatum

/-- Every finite original R1--R3 semigeneric structure strongly amalgamates
over ANY two prescribed induced embeddings. The images meet exactly in
the old base and cover the finite amalgam. -/
theorem finiteRelationalStrongSAP (d : RawDatum G C) :
    d.HasFiniteRelationalStrongSAP := by
  classical
  have hCanonical : HasCanonicalOnePointAgainstFiniteStrongSAP d := by
    intro X hX m P hP B hB hPart hRaw
    exact onePoint_againstCanonicalFinite_strongSAP
      P hP B hB hPart hRaw
  have hLocal : HasOnePointAgainstFiniteStrongSAP d :=
    onePointAgainstFiniteStrongSAP_of_canonical hCanonical
  intro X Y Z _ _ _ A B C₀ hA hB hC f g
  let m : ℕ := finiteExtensionExtraCount f.toFun
  let eB : X ⊕ Fin m ≃ Y :=
    finiteExtensionNormalEquiv f.toFun f.injective
  let P : Structure (rectangleLanguage C) (X ⊕ Fin m) :=
    pullbackRectangle B eB
  have hP : IsRectangleStructure d P := hB.pullback eB
  let T : FiniteRelationalOnePointChain d
      (fun n => PrefixCarrier X m n) :=
    finitePrefixOnePointChain P hP
  let e0 : PrefixCarrier X m 0 ≃ X := prefixInitialEquiv X m
  let eFinal : PrefixCarrier X m m ≃ Y :=
    (prefixFinalEquiv X m).trans eB
  have heOld (a : PrefixCarrier X m 0) :
      eB (prefixToFinal m 0 a) = f (e0 a) := by
    cases a with
    | inl x =>
        change eB (Sum.inl x) = f (e0 (Sum.inl x))
        have h0 : e0 (Sum.inl x) = x :=
          prefixInitialEquiv_inl m x
        rw [h0]
        exact finiteExtensionNormalEquiv_old f.toFun f.injective x
    | inr x =>
        exact Fin.elim0 x
  have hfLang : f.lang = 1 := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  have hgLang : g.lang = 1 := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  have hOldPart (a b : PrefixCarrier X m 0) :
      partRel B (f (e0 a)) (f (e0 b)) ↔
        partRel (T.stage 0) a b := by
    change partRel B (f (e0 a)) (f (e0 b)) ↔
      partRel
        (pullbackRectangle (pullbackRectangle B eB)
          (prefixToFinal m 0)) a b
    simpa only [pullback_partRel, heOld a, heOld b]
  have hOldRaw (c : C) (a b : PrefixCarrier X m 0) :
      rawRel B c (f (e0 a)) (f (e0 b)) ↔
        rawRel (T.stage 0) c a b := by
    change rawRel B c (f (e0 a)) (f (e0 b)) ↔
      rawRel
        (pullbackRectangle (pullbackRectangle B eB)
          (prefixToFinal m 0)) c a b
    simpa only [pullback_rawRel, heOld a, heOld b]
  have hPart0 (a b : PrefixCarrier X m 0) :
      partRel C₀ (g (e0 a)) (g (e0 b)) ↔
        partRel (T.stage 0) a b := by
    calc
      partRel C₀ (g (e0 a)) (g (e0 b)) ↔
          partRel A (e0 a) (e0 b) :=
        embedding_part_iff (rectangleTrivialAction C) A C₀
          g hgLang (e0 a) (e0 b)
      _ ↔ partRel B (f (e0 a)) (f (e0 b)) :=
        (embedding_part_iff (rectangleTrivialAction C) A B
          f hfLang (e0 a) (e0 b)).symm
      _ ↔ partRel (T.stage 0) a b := hOldPart a b
  have hRaw0 (c : C) (a b : PrefixCarrier X m 0) :
      rawRel C₀ c (g (e0 a)) (g (e0 b)) ↔
        rawRel (T.stage 0) c a b := by
    calc
      rawRel C₀ c (g (e0 a)) (g (e0 b)) ↔
          rawRel A c (e0 a) (e0 b) :=
        embedding_raw_iff (rectangleTrivialAction C) A C₀
          g hgLang c (e0 a) (e0 b)
      _ ↔ rawRel B c (f (e0 a)) (f (e0 b)) :=
        (embedding_raw_iff (rectangleTrivialAction C) A B
          f hfLang c (e0 a) (e0 b)).symm
      _ ↔ rawRel (T.stage 0) c a b := hOldRaw c a b
  let g0 : Structure.Embedding (rectangleTrivialAction C)
      (T.stage 0) C₀ :=
    embeddingOfPairwiseEquiv (rectangleTrivialAction C)
      (T.stage 0) C₀
      (fun a => g (e0 a))
      (g.injective.comp e0.injective)
      hPart0 hRaw0
  obtain ⟨W, hW, D, hD, i, j, hSquare⟩ :=
    T.amalgamate_chain_against_finite_exact
      hLocal C₀ hC g0 m le_rfl
  letI : Fintype W := hW
  have hTop : T.stage m = pullbackRectangle B eFinal := by
    change pullbackRectangle (pullbackRectangle B eB)
        (prefixToFinal m m) = pullbackRectangle B eFinal
    rw [pullbackRectangle_comp]
    apply pullbackRectangle_congr
    intro x
    change eB (prefixToFinal m m x) =
      eB (prefixFinalEquiv X m x)
    rw [prefixFinalEquiv_toFinal]
  have hiLang : i.lang = 1 := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  let iB : Structure.Embedding (rectangleTrivialAction C) B D :=
    embeddingOfPairwiseEquiv (rectangleTrivialAction C)
      B D (fun y => i (eFinal.symm y))
      (i.injective.comp eFinal.symm.injective)
      (by
        intro y₁ y₂
        have hp := embedding_part_iff (rectangleTrivialAction C)
          (T.stage m) D i hiLang (eFinal.symm y₁) (eFinal.symm y₂)
        simpa only [hTop, pullback_partRel,
          Equiv.apply_symm_apply] using hp)
      (by
        intro c y₁ y₂
        have hp := embedding_raw_iff (rectangleTrivialAction C)
          (T.stage m) D i hiLang c (eFinal.symm y₁) (eFinal.symm y₂)
        simpa only [hTop, pullback_rawRel,
          Equiv.apply_symm_apply] using hp)
  refine ⟨W, hW, D, hD, iB, j, ?_⟩
  have hTransport :=
    (hSquare.reindexSides eFinal.symm (Equiv.refl Z)).reindexBase e0.symm
  change StrongSquare
    (fun x : X => eFinal (T.fromZero m le_rfl (e0.symm x)))
    (fun x : X => g0 (e0.symm x))
    (fun y : Y => i (eFinal.symm y))
    (fun z : Z => j z) at hTransport
  have hBase0 (x : X) : e0.symm x = Sum.inl x := by
    apply e0.injective
    rw [e0.apply_symm_apply]
    exact (prefixInitialEquiv_inl m x).symm
  have hLeft (x : X) :
      eFinal (T.fromZero m le_rfl (e0.symm x)) = f x := by
    rw [hBase0]
    change eB (prefixFinalEquiv X m
      ((finitePrefixOnePointChain P hP).fromZero m le_rfl (Sum.inl x))) = f x
    rw [prefixFinalEquiv_fromZero_old P hP x]
    exact finiteExtensionNormalEquiv_old f.toFun f.injective x
  have hRight (x : X) : g0 (e0.symm x) = g x := by
    change g (e0 (e0.symm x)) = g x
    rw [e0.apply_symm_apply]
  have hLeftMap :
      (fun x : X => eFinal (T.fromZero m le_rfl (e0.symm x))) =
        (fun x : X => f x) := funext hLeft
  have hRightMap :
      (fun x : X => g0 (e0.symm x)) =
        (fun x : X => g x) := funext hRight
  rw [hLeftMap, hRightMap] at hTransport
  exact hTransport

end RawDatum
end SemigenericEPPA
