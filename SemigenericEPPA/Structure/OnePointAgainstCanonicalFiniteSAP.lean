import SemigenericEPPA.Structure.FinitePrefixBoundaryEquiv
import SemigenericEPPA.Structure.StrongSquareRenaming
import SemigenericEPPA.Structure.RelativeOnePointSAP
import SemigenericEPPA.Structure.PairwiseEmbedding

/-!
# A one-point original-relational extension against any canonical finite extension

The certified one-point-chain construction works on canonical prefix
carriers X ⊕ Fin (min n m) whose initial stage is X ⊕ Fin 0.
Here we use the exact endpoint equivalences to convert its result into
the literal strong amalgamation square for:

  A on X,
  B on Option X extending A on its some vertices,
  P on X ⊕ Fin m extending A on its Sum.inl vertices.

Every map is an actual AllThoseEPPA structure embedding in the
ORIGINAL binary E/R_c language. Overlap is exactly the old X;
the amalgam is jointly covered by the two given sides.
Nothing assumes involution safety, DLF, or coherent EPPA.

The final step from arbitrary named finite Y,Z to Option X and
X ⊕ Fin m is separate, via finiteExtensionNormalEquiv.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}

/-- An arbitrary one-point extension of X strongly amalgamates
against an arbitrary ORIGINAL finite R1--R3 extension on X ⊕ Fin m.
The old vertices are literally some x and Sum.inl x. -/
theorem onePoint_againstCanonicalFinite_strongSAP
    {X : Type (max u v)} [Fintype X] {m : ℕ}
    (P : Structure (rectangleLanguage C) (X ⊕ Fin m))
    (hP : IsRectangleStructure d P)
    (B : Structure (rectangleLanguage C) (Option X))
    (hB : IsRectangleStructure d B)
    (hPart : ∀ x y : X,
      partRel B (some x) (some y) ↔
        partRel P (Sum.inl x) (Sum.inl y))
    (hRaw : ∀ (c : C) (x y : X),
      rawRel B c (some x) (some y) ↔
        rawRel P c (Sum.inl x) (Sum.inl y)) :
    ∃ (W : Type (max u v)) (hW : Fintype W)
      (D : Structure (rectangleLanguage C) W),
      IsRectangleStructure d D ∧
      ∃ (i : Structure.Embedding (rectangleTrivialAction C) B D)
        (j : Structure.Embedding (rectangleTrivialAction C) P D),
        StrongSquare
          (fun x : X => (some x : Option X))
          (fun x : X => (Sum.inl x : X ⊕ Fin m))
          (fun b => i b) (fun p => j p) := by
  classical
  let e0 : PrefixCarrier X m 0 ≃ X := prefixInitialEquiv X m
  let eB : Option (PrefixCarrier X m 0) ≃ Option X := e0.optionCongr
  let B0 : Structure (rectangleLanguage C)
      (Option (PrefixCarrier X m 0)) := pullbackRectangle B eB
  have hB0 : IsRectangleStructure d B0 := hB.pullback eB
  have hB0Part : ∀ a b : PrefixCarrier X m 0,
      partRel B0 (some a) (some b) ↔
        partRel (prefixStructure P 0) a b := by
    intro a b
    cases a with
    | inl x =>
        cases b with
        | inl y =>
            change partRel B (eB (some (Sum.inl x))) (eB (some (Sum.inl y))) ↔
              partRel P (Sum.inl x) (Sum.inl y)
            have hx : eB (some (Sum.inl x)) = some x := by
              change some (e0 (Sum.inl x)) = some x
              rw [prefixInitialEquiv_inl]
            have hy : eB (some (Sum.inl y)) = some y := by
              change some (e0 (Sum.inl y)) = some y
              rw [prefixInitialEquiv_inl]
            rw [hx, hy]
            exact hPart x y
        | inr i => exact Fin.elim0 i
    | inr i => exact Fin.elim0 i
  have hB0Raw : ∀ (c : C) (a b : PrefixCarrier X m 0),
      rawRel B0 c (some a) (some b) ↔
        rawRel (prefixStructure P 0) c a b := by
    intro c a b
    cases a with
    | inl x =>
        cases b with
        | inl y =>
            change rawRel B c (eB (some (Sum.inl x))) (eB (some (Sum.inl y))) ↔
              rawRel P c (Sum.inl x) (Sum.inl y)
            have hx : eB (some (Sum.inl x)) = some x := by
              change some (e0 (Sum.inl x)) = some x
              rw [prefixInitialEquiv_inl]
            have hy : eB (some (Sum.inl y)) = some y := by
              change some (e0 (Sum.inl y)) = some y
              rw [prefixInitialEquiv_inl]
            rw [hx, hy]
            exact hRaw c x y
        | inr i => exact Fin.elim0 i
    | inr i => exact Fin.elim0 i
  obtain ⟨W, hW, D, hD, i0, j0, hSq⟩ :=
    canonicalOnePoint_againstFinitePrefix P hP B0 hB0 hB0Part hB0Raw
  letI : Fintype W := hW
  let eFinal : PrefixCarrier X m m ≃ X ⊕ Fin m :=
    prefixFinalEquiv X m
  have hPFinal : prefixStructure P m = pullbackRectangle P eFinal := by
    have heq : prefixToFinal m m = eFinal := by
      funext z
      exact (prefixFinalEquiv_toFinal X m z).symm
    change pullbackRectangle P (prefixToFinal m m) =
      pullbackRectangle P eFinal
    rw [heq]
  have hli0 : i0.lang = 1 := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  have hlj0 : j0.lang = 1 := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  let i : Structure.Embedding (rectangleTrivialAction C) B D :=
    embeddingOfPairwiseEquiv (rectangleTrivialAction C) B D
      (fun x => i0 (eB.symm x))
      (i0.injective.comp eB.symm.injective)
      (by
        intro x y
        have hp := embedding_part_iff (rectangleTrivialAction C)
          B0 D i0 hli0 (eB.symm x) (eB.symm y)
        simpa only [B0, pullback_partRel, Equiv.apply_symm_apply] using hp)
      (by
        intro c x y
        have hp := embedding_raw_iff (rectangleTrivialAction C)
          B0 D i0 hli0 c (eB.symm x) (eB.symm y)
        simpa only [B0, pullback_rawRel, Equiv.apply_symm_apply] using hp)
  let j : Structure.Embedding (rectangleTrivialAction C) P D :=
    embeddingOfPairwiseEquiv (rectangleTrivialAction C) P D
      (fun x => j0 (eFinal.symm x))
      (j0.injective.comp eFinal.symm.injective)
      (by
        intro x y
        have hp := embedding_part_iff (rectangleTrivialAction C)
          (prefixStructure P m) D j0 hlj0 (eFinal.symm x) (eFinal.symm y)
        simpa only [hPFinal, pullback_partRel, Equiv.apply_symm_apply] using hp)
      (by
        intro c x y
        have hp := embedding_raw_iff (rectangleTrivialAction C)
          (prefixStructure P m) D j0 hlj0 c (eFinal.symm x) (eFinal.symm y)
        simpa only [hPFinal, pullback_rawRel, Equiv.apply_symm_apply] using hp)
  refine ⟨W, hW, D, hD, i, j, ?_⟩
  let T := finitePrefixOnePointChain P hP
  have hTransport :=
    (hSq.reindexSides eB.symm eFinal.symm).reindexBase e0.symm
  change StrongSquare
    (fun x : X => eB (some (e0.symm x)))
    (fun x : X => eFinal (T.fromZero m le_rfl (e0.symm x)))
    (fun x : Option X => i0 (eB.symm x))
    (fun x : X ⊕ Fin m => j0 (eFinal.symm x)) at hTransport
  have hBase0 (x : X) : e0.symm x = Sum.inl x := by
    apply e0.injective
    rw [e0.apply_symm_apply]
    exact (prefixInitialEquiv_inl m x).symm
  have hLeft : (fun x : X => eB (some (e0.symm x))) =
      (fun x : X => some x) := by
    funext x
    change some (e0 (e0.symm x)) = some x
    rw [e0.apply_symm_apply]
  have hRight :
      (fun x : X => eFinal (T.fromZero m le_rfl (e0.symm x))) =
      (fun x : X => (Sum.inl x : X ⊕ Fin m)) := by
    funext x
    rw [hBase0]
    exact prefixFinalEquiv_fromZero_old P hP x
  rw [hLeft, hRight] at hTransport
  exact hTransport

end SemigenericEPPA
