import SemigenericEPPA.Structure.FiniteSAPFromOnePointFinite
import SemigenericEPPA.Structure.FiniteExtensionNormalForm
import SemigenericEPPA.Structure.OnePointNormalization
import SemigenericEPPA.Structure.RelativeOnePointSAP
import SemigenericEPPA.Structure.StrongSquareRenaming

/-!
# Transport canonical one-point-vs-finite SAP to ANY actual finite span

Suppose the canonical original R1--R3 strong-amalgamation theorem holds
for a one-point B on Option X and an arbitrary finite extension P on
X ⊕ Fin m, both literally agreeing on the common old vertices X.

For arbitrary finite actual E/R_c structures A, B, D and genuine
induced embeddings f : A → B, g : A → D, when B/A is one-point,
we canonically normalize:
- B to Option A via its true distinguished fresh vertex;
- D to A ⊕ Fin m by enumerating exactly D \ g(A).

We then invoke the canonical strong square, and REINDEX BOTH SIDES
using the actual bijections. The result retains the SPECIFIED f,g,
genuine typed embeddings, exact intersection and joint coverage.
No local involution safety, DLF, or stronger ambient hypotheses.

This lemma is mathematically unconditional in its transportation:
the canonical hypothesis is explicitly exposed and will be discharged
by the finite prefix chain construction in the neighboring SAP branch.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v

variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}

/-- The exact canonical finite-amalgamation statement:
one original one-point extension on Option X versus ANY finite
original extension on X ⊕ Fin m, with the specified old maps,
an actual finite original-language witness, and a strong square. -/
def HasCanonicalOnePointAgainstFiniteStrongSAP
    (d : RawDatum G C) : Prop :=
  ∀ {X : Type (max u v)} [Fintype X] {m : ℕ}
    (P : Structure (rectangleLanguage C) (X ⊕ Fin m))
    (hP : IsRectangleStructure d P)
    (B : Structure (rectangleLanguage C) (Option X))
    (hB : IsRectangleStructure d B)
    (hPart : ∀ x y : X,
      partRel B (some x) (some y) ↔
        partRel P (Sum.inl x) (Sum.inl y))
    (hRaw : ∀ (c : C) (x y : X),
      rawRel B c (some x) (some y) ↔
        rawRel P c (Sum.inl x) (Sum.inl y)),
    ∃ (W : Type (max u v)) (hW : Fintype W)
      (S : Structure (rectangleLanguage C) W),
      IsRectangleStructure d S ∧
      ∃ (i : Structure.Embedding (rectangleTrivialAction C) B S)
        (j : Structure.Embedding (rectangleTrivialAction C) P S),
        StrongSquare
          (fun x : X => (some x : Option X))
          (fun x : X => (Sum.inl x : X ⊕ Fin m))
          (fun b => i b) (fun p => j p)

/-- The canonical finite one-point-vs-finite theorem implies the
FULL relative version with ARBITRARILY NAMED finite carriers and
actual prescribed induced old embeddings. This is the exact missing
normalization bridge, not an assumption on semigeneric structures. -/
theorem onePointAgainstFiniteStrongSAP_of_canonical
    (hCanon : HasCanonicalOnePointAgainstFiniteStrongSAP d) :
    HasOnePointAgainstFiniteStrongSAP d := by
  classical
  intro X Y Z _ _ _ A B D hA hB hD f g fresh hFresh hCover
  let eB : Option X ≃ Y :=
    onePointCarrierEquiv f.toFun f.injective fresh hFresh hCover
  let m : ℕ := finiteExtensionExtraCount g.toFun
  let eD : X ⊕ Fin m ≃ Z :=
    finiteExtensionNormalEquiv g.toFun g.injective
  let Bnorm : Structure (rectangleLanguage C) (Option X) :=
    pullbackRectangle B eB
  let Dnorm : Structure (rectangleLanguage C) (X ⊕ Fin m) :=
    pullbackRectangle D eD
  have hBn : IsRectangleStructure d Bnorm := hB.pullback eB
  have hDn : IsRectangleStructure d Dnorm := hD.pullback eD
  have hLangF : f.lang = 1 := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  have hLangG : g.lang = 1 := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  have heB (x : X) : eB (some x) = f x := by
    exact onePointCarrierEquiv_some f.toFun f.injective
      fresh hFresh hCover x
  have heD (x : X) : eD (Sum.inl x) = g x := by
    exact finiteExtensionNormalEquiv_old g.toFun g.injective x
  have hPart : ∀ x y : X,
      partRel Bnorm (some x) (some y) ↔
        partRel Dnorm (Sum.inl x) (Sum.inl y) := by
    intro x y
    change partRel B (eB (some x)) (eB (some y)) ↔
      partRel D (eD (Sum.inl x)) (eD (Sum.inl y))
    rw [heB x, heB y, heD x, heD y]
    exact (embedding_part_iff (rectangleTrivialAction C)
      A B f hLangF x y).trans
      (embedding_part_iff (rectangleTrivialAction C)
        A D g hLangG x y).symm
  have hRaw : ∀ (c : C) (x y : X),
      rawRel Bnorm c (some x) (some y) ↔
        rawRel Dnorm c (Sum.inl x) (Sum.inl y) := by
    intro c x y
    change rawRel B c (eB (some x)) (eB (some y)) ↔
      rawRel D c (eD (Sum.inl x)) (eD (Sum.inl y))
    rw [heB x, heB y, heD x, heD y]
    exact (embedding_raw_iff (rectangleTrivialAction C)
      A B f hLangF c x y).trans
      (embedding_raw_iff (rectangleTrivialAction C)
        A D g hLangG c x y).symm
  obtain ⟨W, hW, S, hS, iNorm, jNorm, hSquare⟩ :=
    hCanon Dnorm hDn Bnorm hBn hPart hRaw
  let i : Structure.Embedding (rectangleTrivialAction C) B S :=
    iNorm.comp
      (RelativeOnePointDiagram.inversePullbackEmbedding
        (rectangleTrivialAction C) B eB)
  let j : Structure.Embedding (rectangleTrivialAction C) D S :=
    jNorm.comp
      (RelativeOnePointDiagram.inversePullbackEmbedding
        (rectangleTrivialAction C) D eD)
  refine ⟨W, hW, S, hS, i, j, ?_⟩
  have hTransport := hSquare.reindexSides eB.symm eD.symm
  change StrongSquare
    (fun x : X => eB (some x))
    (fun x : X => eD (Sum.inl x))
    (fun y : Y => iNorm (eB.symm y))
    (fun z : Z => jNorm (eD.symm z)) at hTransport
  have hOldB : (fun x : X => eB (some x)) = (fun x : X => f x) :=
    funext heB
  have hOldD : (fun x : X => eD (Sum.inl x)) = (fun x : X => g x) :=
    funext heD
  rw [hOldB, hOldD] at hTransport
  exact hTransport

end SemigenericEPPA
