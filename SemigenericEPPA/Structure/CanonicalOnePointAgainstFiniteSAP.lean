import SemigenericEPPA.Structure.FinitePrefixOnePointChain
import SemigenericEPPA.Structure.FiniteChainExactBaseMap
import SemigenericEPPA.Structure.PairwiseEmbedding

/-!
# One original one-point extension against an arbitrary finite prefix

Let P be any R1--R3 original-language structure on X ⊕ Fin m.
Its induced canonical prefix chain begins at X ⊕ Fin 0 and ends
at a structure isomorphic to P. Given a genuine one-point
extension B of the initial prefix, we construct an exact strong
amalgamation of B with the last prefix.

The common-base embedding in the terminal strong square is
the ACTUAL prescribed composite of prefix inclusions, rather
than some independently chosen old-image embedding.

The still separate transport from X ⊕ Fin m to an arbitrarily
named original finite extension uses the finite-complement
normalization and strong-square reindexing theorems.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}

/-- A genuine one-point extension of the initial prefix of ANY
finite original E/R_c rectangle strongly amalgamates against its
full canonical finite prefix chain, with the PRECISE old map.

No safety, DLF, coherent-EPPA, or additional algebraic hypothesis. -/
theorem canonicalOnePoint_againstFinitePrefix
    {X : Type (max u v)} [Fintype X] {m : ℕ}
    (P : Structure (rectangleLanguage C) (X ⊕ Fin m))
    (hP : IsRectangleStructure d P)
    (B : Structure (rectangleLanguage C)
      (Option (PrefixCarrier X m 0)))
    (hB : IsRectangleStructure d B)
    (hPart : ∀ a b : PrefixCarrier X m 0,
      partRel B (some a) (some b) ↔
        partRel (prefixStructure P 0) a b)
    (hRaw : ∀ (c : C) (a b : PrefixCarrier X m 0),
      rawRel B c (some a) (some b) ↔
        rawRel (prefixStructure P 0) c a b) :
    ∃ (W : Type (max u v)) (hW : Fintype W)
      (D : Structure (rectangleLanguage C) W),
      IsRectangleStructure d D ∧
      ∃ (i : Structure.Embedding (rectangleTrivialAction C) B D)
        (j : Structure.Embedding (rectangleTrivialAction C)
          (prefixStructure P m) D),
        StrongSquare
          (fun a : PrefixCarrier X m 0 => (some a : Option _))
          (fun a : PrefixCarrier X m 0 =>
            (finitePrefixOnePointChain P hP).fromZero m le_rfl a)
          (fun b => i b) (fun c => j c) := by
  classical
  let T := finitePrefixOnePointChain P hP
  let f : Structure.Embedding (rectangleTrivialAction C)
      (T.stage 0) B :=
    embeddingOfPairwiseEquiv (rectangleTrivialAction C)
      (T.stage 0) B Option.some
      (by intro x y h; exact Option.some.inj h) hPart hRaw
  have hOutside : ∀ x : PrefixCarrier X m 0,
      f x ≠ (none : Option (PrefixCarrier X m 0)) := by
    intro x
    simp [f, embeddingOfPairwiseEquiv]
  have hCover : ∀ b : Option (PrefixCarrier X m 0),
      b = none ∨ ∃ x : PrefixCarrier X m 0, f x = b := by
    intro b
    cases b with
    | none => exact Or.inl rfl
    | some x => exact Or.inr ⟨x, rfl⟩
  obtain ⟨W, hW, D, hD, i, j, hSquare⟩ :=
    T.amalgamate_onePoint_against_chain_exact
      B hB f none hOutside hCover m le_rfl
  exact ⟨W, hW, D, hD, i, j, hSquare⟩

end SemigenericEPPA
