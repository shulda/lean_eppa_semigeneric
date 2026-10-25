# Finite SAP iteration — exact proof handoff (25 October 2026)

This document records the remaining mathematical/Lean gap in the original
R1–R3 strong amalgamation theorem. **Do not claim full arbitrary finite
SAP until its final theorem has passed a complete Lean CI and axiom audit.**

## Certified lemmas

- `Structure/LiteralSAPEmbeddings.lean` proves one-point strong SAP for
  two original relational one-point extensions, with genuine
  `AllThoseEPPA.Structure.Embedding` maps and exact intersection.
- `Structure/RelativeOnePointSAP.lean` handles arbitrarily named
  one-point carriers and shows the amalgam is covered by both images.
- `Structure/StrongSquare.lean` defines exact, jointly surjective
  strong squares and verifies pasting.
- `Structure/OnePointSquarePasting.lean` proves
  `strongSquare_extend_right_onePoint`: if a strong square amalgamates
  a one-point B/A against a finite C/A, adjoining a new point to C
  extends the strong square without introducing any identifications.
  **Full CI/audit passed on PR #574**, merged into main.
- `Structure/OnePointChainSAP.lean` proves
  `FiniteRelationalOnePointChain.amalgamate_onePoint_against_chain`,
  inductively amalgamating one fixed one-point extension against a
  finite one-point chain of genuine original R1–R3 structures.
  **Full CI/audit passed on PR #575**, merged into main.

## New branches being tested

- **PR #577:** `FinitePrefixOnePointChain.lean` constructs an explicit
  length-m induced chain for an arbitrary finite original structure on
  X ⊕ Fin m. At index n the carrier is X ⊕ Fin (min n m), with exact
  E / every ordered R_c embeddings and no extra vertices. The
  initial carrier X ⊕ Fin 0 is canonically equivalent to X, and
  the final carrier X ⊕ Fin m to the input. This is not yet part of
  main until its full CI passes.

## Terminal goal

For arbitrary finite original R1–R3 structures A,B,C and induced
identity-language embeddings f:A→B and g:A→C, construct a finite
R1–R3 structure D and induced embeddings i:B→D, j:C→D such that

    i ∘ f = j ∘ g
    i(b) = j(c) ↔ ∃a, b=f(a) ∧ c=g(a)

We additionally target joint surjectivity of i and j (a carrier
that is precisely a strong pushout), avoiding dummy points.

## Mathematical algorithm: finite grid of one-point strong squares

1. Enumerate B \ f(A) and C \ g(A). Use an actual bijection of
   each complement with Fin k and finite-carrier pullbacks to obtain
   canonical finite chains B_0 ⊆ ... ⊆ B_b=B and
   C_0 ⊆ ... ⊆ C_c=C. Here B_0=C_0=A, up to fixed induced
   equivalences. No extra ordering on E-classes or colours.
2. Construct structures D_{i,j}, with bottom row D_{i,0}=B_i and
   left column D_{0,j}=C_j, preserving the entire induced prefix
   diagrams and their transition maps.
3. For i,j>0, D_{i-1,j} and D_{i,j-1} are ONE-POINT extensions
   of D_{i-1,j-1}; apply the certified relative one-point strong SAP
   theorem to obtain D_{i,j}. Their images meet in exactly
   D_{i-1,j-1}; the output is covered by those images.
4. Paste the strong squares along grid rows/columns. This gives
   D_{b,c} with exact original A overlap and no identification of
   any vertex outside A. All E and every ordered R_c are preserved
   and reflected at every step.
5. Transport along the complement enumerations to recover the
   original arbitrarily named B,C with the original embeddings.
   Use `pullbackRectangle`, `pullbackRectangle_embedding`,
   `RelativeOnePointDiagram.inversePullbackEmbedding`, and
   `embeddingOfPairwiseEquiv` to avoid any implicit replacement
   of the true original relational class.

**Key remaining Lean engineering:** the existing
`amalgamate_onePoint_against_chain` produces a strong square
independently at every finite prefix; for the *second* induction
over the other side, retain a coherent full row of squares and
one-point transition maps as a structured output. A dependent row
construction (or equivalent well-founded finite-grid recursion) is
needed. Do not infer coherence of existentially chosen stages
without explicit compatible embeddings.

Once this terminal SAP theorem is green, its unconditional version
can be used with existing hereditary/JEP lemmas for a Fraïssé
construction. The separate general Sági equivalence is intentionally
out of scope. A standalone uniqueness theorem can be added only if
the mismatch between this project's `AllThoseEPPA.Language` and
Mathlib's `FirstOrder.Language` can be bridged economically.
