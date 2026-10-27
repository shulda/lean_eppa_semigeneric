# Independent manuscript-to-Lean statement audit — Appendix A

Date: 2026-10-27. Source: private group-valued-rectangles formalization draft v0.8, optional Appendix A. Public target: `SemigenericEPPA/Classification/MainClassification.lean`.

## Verdict and exact scope

Appendix A classifies **finite unrestricted binary equivalence-and-cross-colour ages constrained only by isomorphism-invariant 2+2 rectangles and satisfying strong amalgamation**. It does NOT classify every homogeneous structure with extra triangle constraints, nor merely AP classes.

| Manuscript ingredient | Literal Lean counterpart | Audit conclusion |
| --- | --- | --- |
| Finite nonempty raw colour alphabet $C$ | `[Finite C]`, `[Nonempty C]` on `finiteStrongSAP_iff_groupRectangle` | Exact |
| Involution $c\mapsto c^*$ | `RectangleRule.reverse`, `reverse_involutive` | Exact |
| Rectangle isomorphism invariance | `row_swap`, `col_swap`, `starred_transpose` | Exact |
| Unrestricted triangle base | `IsRuleStructure.parts_equiv`, `raw_only_cross`, `cross_unique`, `reverse`; **no other axioms** | Exact |
| Genuine $2+2$ constraints | `IsRuleStructure.rectangle` requests `x₀ ≠ x₁` and `y₀ ≠ y₁` | Exact, important: no accidental degenerate constraints on arbitrary P |
| Original finite SAP, given embeddings | `RectangleRule.HasFiniteRuleStrongSAP` and `StrongSquare` | Exact induced $E,R_c$ embeddings, overlap, and union coverage |
| Necessity of row amalgamation | `SAPRowAmalgamation.rowAmalgamation_of_finiteRuleStrongSAP` | Uses actual `StrongSquare.exact_overlap`; cannot replace SAP by AP |
| Necessity of corner completion | `SAPCornerCompletion.cornerCompletion_of_finiteRuleStrongSAP` | Uses actual finite relational amalgam |
| Reconstruction of quotient/torsor | `RectangleDisplacements`, `DisplacementTranslations` | No pre-existing group assumed; exact displacement equality |
| Finite noncommutative group $G$ | `ReconstructedGroup`, `reconstructedGroup_finite` | Derived from surjection of finite $C$; no commutativity |
| Affine anti-involution, not normalized | `AffineClassification.reconstructedAffineAntiInvolution` | Involutive and $s(xy)=s(y)s(1)^{-1}s(x)$ |
| Equivariant surjection $\phi$ | `reconstructedRawDatum`, `reconstructedPhi_surjective` | Exact original alphabet and $\phi(c^*)=s(\phi(c))$ |
| **Preservation of given reversal** | `HasGroupRectangleDescription` conjunct `d.reverse = R.reverse` | An earlier looser endpoint was discovered during independent audit and **tightened** |
| Exact $P$ equation | `allowed_iff_reconstructedRawDatum` and `finiteStrongSAP_iff_groupRectangle` | $\phi(a)^{-1}\phi(b)=\phi(c)^{-1}\phi(d)$, with ordered colours |
| Reverse direction SAP | `isRuleStructure_iff_reconstructedGroup`, existing `RawDatum.finiteRelationalStrongSAP` | Original binary structures, not just effective matrix algebra |

## Logical dependence and caveats

The algebraic module assumes row amalgamation and corner completion **only internally**. The final theorem deduces them from `HasFiniteRuleStrongSAP` before invoking that module. Therefore there is no assumption of the desired classification hidden in its definition.

The finite original-class SAP predicate is deliberately **exact**: the chosen copies cover the amalgam in addition to meeting only in the base. This is mathematically equivalent to ordinary strong amalgamation for the hereditary finite relational $\mathcal K_P$, by passing from an arbitrary strong amalgam to the induced substructure on the union. This elementary equivalence of two SAP formulations is not a separate general Lean theorem in this library.

The final theorem is a classification of the **ages** $\mathcal K_P$; by standard Fraïssé theory a countable homogeneous limit follows once JEP is observed, but it is not claiming an independent Lean formalization of the general Fraïssé theorem.

No manuscript TeX or unpublished proof text is included in this public file. On the target branch, the complete appendix classifier passed the focused GitHub CI build at `fb0e33293e`. The full root-library build and axiom audit subsequently **passed** on [`70ae457a`](https://github.com/shulda/lean_eppa_semigeneric/commit/70ae457aa0264af70b01d07844dcfac2109b6c5b), [GitHub Actions #40465889222](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40465889222): **1,861 jobs built; 4,050 declarations audited; permitted axioms only `propext`, `Classical.choice`, `Quot.sound`**. This certificate covers the restored full root import, not just the earlier focused run.

## Acceptance checklist

- [x] Concrete original-language SAP-to-row and SAP-to-corner proofs compile.
- [x] Quotient, Latin and group/torsor reconstruction compile.
- [x] Affine anti-involution, surjective equivariant map and finite group compile.
- [x] Exact original-$P$ relational class correspondence compiles.
- [x] Final iff with required identical raw reversal compiles on focused CI.
- [x] Full root library build and axiom audit passed at integrated code SHA `70ae457a`, [CI #40465889222](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40465889222).
- [x] Independent source-facing review of the exact Lean statement and its definitions completed; the original reversal conjunct was strengthened during audit.
