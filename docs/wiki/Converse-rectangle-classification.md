# Appendix A — converse classification of SAP rectangle laws

The article's optional Appendix A asks whether the group-valued rectangle construction is **forced** by strong amalgamation, rather than merely being a family of examples. Its answer is **yes, under the exact hypotheses below**, and the public Lean library now formalizes both implications.

## Human mathematical statement

Fix a finite, nonempty palette \(C\), an involution \(c\mapsto c^*\), and an arbitrary predicate \(P(a,b,c,d)\) specifying allowed \(2+2\) rectangles. We assume only the isomorphism symmetries
\[
P(a,b,c,d)\Longleftrightarrow P(c,d,a,b)
\Longleftrightarrow P(b,a,d,c),\qquad
P(a,b,c,d)\Longleftrightarrow P(a^*,c^*,b^*,d^*).
\]

The original binary language has an equivalence relation \(E\) and one directed relation \(R_c\) per colour. A finite structure belongs to \(\mathcal K_P\) when every ordered cross-\(E\)-class pair has exactly one raw colour, reverse pairs use \(c^*\), and every actual \(2+2\) rectangle with **distinct** vertices in each part satisfies \(P\). There are **no additional triangle constraints**.

Then \(\mathcal K_P\) has **strong amalgamation** precisely when there are a finite group \(G\), an affine anti-involution \(s:G\to G\), and a surjective map \(\phi:C\to G\) for which
\[
\phi(c^*)=s(\phi(c)),\qquad
P(a,b,c,d)\Longleftrightarrow
\phi(a)^{-1}\phi(b)=\phi(c)^{-1}\phi(d).
\]
The group may be nonabelian and \(s(1)\) need not equal \(1\). Intrinsically, the quotient palette is a **torsor**; choosing an origin produces the group.

The exact formal endpoint is [`RectangleRule.finiteStrongSAP_iff_groupRectangle`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/MainClassification.lean). The right-hand predicate [`HasGroupRectangleDescription`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/MainClassification.lean) includes `d.reverse = R.reverse` in addition to the group equation, so the classifier cannot silently change the original reversal.

## Proof-to-Lean map

| Mathematical step | Certified declaration / file | What is *actually* proved |
| --- | --- | --- |
| Arbitrary rectangle symmetries and \(P\)-structures | [`RectangleRule` / `IsRuleStructure`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/GeneralRuleStructure.lean) and [symmetries](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/RectangleDisplacements.lean) | Literal original \(E,R_c\) semantics, distinct \(2+2\) rectangles, unrestricted triangles |
| Matrix structures and embeddings | [`RuleMatrixPresentation`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/RuleMatrixPresentation.lean), [`RuleMatrixEmbedding`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/RuleMatrixEmbedding.lean) | Actual induced embeddings, including both directions of every \(R_c\) |
| SAP implies corner completion | [`cornerCompletion_of_finiteRuleStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/SAPCornerCompletion.lean) | Amalgamate adding one new row vertex and one new column vertex to a prescribed cross-pair |
| SAP implies row amalgamation | [`rowAmalgamation_of_finiteRuleStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/SAPRowAmalgamation.lean) | Amalgamate two extensions sharing one row; **exact overlap keeps the two new rows distinct** |
| Displacements and effective palette | [`RectangleDisplacements`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/RectangleDisplacements.lean) | \(P\) defines a setoid on \(C^2\), an invisible-colour quotient \(C/{\sim}\), Latin rows and pasting |
| Group/torsor reconstruction | [`DisplacementTranslations`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/DisplacementTranslations.lean) | A regular group of displacement-preserving permutations, exact noncommutative difference identity |
| Reversal and raw datum | [`AffineClassification`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/AffineClassification.lean) | Affine anti-involution, surjective equivariant \(\phi\), finiteness from finite \(C\) |
| Converse SAP and final iff | [`GeneralRuleStructure`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/GeneralRuleStructure.lean), [`MainClassification`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/MainClassification.lean) | Reuse the already proved original-language finite SAP; quantify a real SAP predicate, not the two consequences |

## Scope and independent checks

The formal strong-square interface demands that the embedded images meet **exactly** in the given base and jointly cover the amalgam. Joint coverage is harmless here: the age is hereditary, and any ordinary strong amalgam can be restricted to the induced union of the two embedded structures. The theorem therefore has the intended usual finite SAP meaning, but does **not** assert ordinary AP alone suffices.

The general predicate \(P\) has no conditions on degenerate \(2+2\) matrices: distinctness is required in the source class. When \(P\) is reconstructed from a group, the corresponding equality automatically extends to degenerate instances. No extra triangle, row-composition or forbidden-cycle constraints are included.

The proof is independent of finite EPPA, coherent EPPA, DLF and Sági's theorem. The pre-existing group-valued original-relational SAP theorem is reused for the sufficiency direction only. An abstract general Fraïssé uniqueness/existence theorem is not part of this Appendix A formalization.

See the [independent adversarial audit](Adversarial-audit.md) and the [main theorem overview](Main-theorems.md). The source-facing checklist is also preserved as `CLASSIFICATION_STATEMENT_AUDIT_2026-10-27.md` in the repository.
