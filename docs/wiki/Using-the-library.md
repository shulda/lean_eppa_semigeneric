# Using the public Lean library

The project is built with Lean and Mathlib **v4.34.1**, and depends on a pinned public revision of `AllThoseEPPA` for its language, embedding and coherence vocabulary. It does **not** assume the general HKN/Herwig–Lascar EPPA theorems.

## Get a reproducible version

To reproduce the audited mathematical results, check out public [commit `df21cfa98a66`](https://github.com/shulda/lean_eppa_semigeneric/commit/df21cfa98a668e1a95dceb73ce83d852336e6842):

~~~bash
git clone https://github.com/shulda/lean_eppa_semigeneric.git
cd lean_eppa_semigeneric
git checkout df21cfa98a668e1a95dceb73ce83d852336e6842
lake exe cache get
lake build
~~~

The corresponding [CI run](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40344432058) completed successfully with the allowed-axiom audit.

To depend on that fixed version from another Lake project, use the same Lean toolchain and add the following to `lakefile.toml`:

~~~toml
[[require]]
name = "SemigenericEPPA"
git = "https://github.com/shulda/lean_eppa_semigeneric.git"
rev = "df21cfa98a668e1a95dceb73ce83d852336e6842"
~~~

The Mathlib and `AllThoseEPPA` revisions are pinned by the upstream `lake-manifest.json`. Avoid silently changing those revisions when reproducing an audit.

## Main theorem checks

~~~lean
import SemigenericEPPA

open SemigenericEPPA

#check SemigenericEPPA.RawDatum.finiteRelationalStrongSAP
#check SemigenericEPPA.RawDatum.finiteRelationalJEP
#check SemigenericEPPA.IsRectangleStructure.finite_relationalRawEPPA_witness
#check SemigenericEPPA.RawRectanglePresentation.finite_typedEPPA_witness
#check SemigenericEPPA.RawDatum.hasFiniteRelationalCoherentEPPAInCanonicalUniverses_iff
#check SemigenericEPPA.RawDatum.finiteRelationalSemiCoherentEP_iff_relationalDLF
#check SemigenericEPPA.RawDatum.countableRelationalHomogeneousDLF_iff
#check SemigenericEPPA.FourColourSeparation.semiCoherentDLFNotCoherent
~~~

For the theorem bodies and definitions, follow [Main theorems](Main-theorems.md). When reusing a class predicate, inspect its definition rather than inferring its quantifiers from its name.

## Newer original-relational convenience API

Two directly source-facing lemmas were added **after** the pinned `df21cfa9` baseline, with a separate successful [full CI/axiom audit on PR #601](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40349653163). To use them, select commit [`e094e5c0`](https://github.com/shulda/lean_eppa_semigeneric/commit/e094e5c094de1909df70ef8267258e2d92c3f49b) or a later verified revision:

~~~lean
import SemigenericEPPA

#check SemigenericEPPA.IsRectangleStructure.finite_relationalTypedEPPA_witness
#check SemigenericEPPA.FourColourSeparation.nativeSemiCoherentDLFNotCoherent
~~~

The first is a genuinely typed original `E/R_c` EPPA witness without manually rewriting the source to its raw presentation. The second packages the strict `C_4` example entirely with native original-relational predicates.

## Three example tasks

**Prove finite SAP for your raw datum.** If `d : RawDatum G C`, the expression `d.finiteRelationalStrongSAP` has the exact property `d.HasFiniteRelationalStrongSAP`. It needs no additional good-colour or DLF assumption.

**Get ordinary EPPA for a finite old structure.** If `h : IsRectangleStructure d A` with the required finite parameter and vertex types, `h.finite_relationalRawEPPA_witness` returns the finite witness, the fixed induced embedding, and the extension property for **all** partial maps. If a typed witness is needed, use the typed `RawRectanglePresentation.finite_typedEPPA_witness` after the exact roundtrip theorem.

**Decide coherent EPPA or DLF.** Use the appropriate classification equivalence and prove the right-hand group condition: global saturation + nonemptiness for coherent EPPA, versus one complete good orbit for DLF. Both accept the trivial $G$ branch even if there are no self-reversing raw colours.

For the **concrete** separation, inspect [`FourColourDLFNotCoherent.lean`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean).

## Documented omissions

This is a reusable finite EPPA and DLF research library, **not** a generic automated Fraïssé functor. The abstract theorem identifying an arbitrary constructed homogeneous full-age structure with the uniquely named Fraïssé limit is not an exported endpoint. A general Sági equivalence for unrelated classes and the converse classification of abstract rectangle laws are outside this library's stated scope.
