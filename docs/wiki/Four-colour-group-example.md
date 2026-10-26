# A strict separation example based on the cyclic group of order four

This is a concrete **verified datum**, not an existential assertion deduced from the group classification without specifying a raw palette.

## The data

Let $G=C_4=\mathbb Z/4\mathbb Z$, written additively for readability, and take $s=\mathrm{id}$ (legitimate as an affine anti-involution because $G$ is abelian). Choose **five** raw colours $0,1,2,3,4$, with

- $\phi(0)=0,\ \phi(1)=1,\ \phi(2)=2,\ \phi(3)=\phi(4)=3$;
- raw reversal fixing $0,1,2$ and swapping $3\leftrightarrow4$.

In Lean these are [`FourColourSeparation.G4`, `identityReversal`, `rawReverse`, `rawPhi` and `c4Datum`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean). The code checks involutivity, surjectivity and equivariance.

The self-reversing effective colours form
$$ S=\{0,1,2\}. $$
Since $s=\mathrm{id}$, the affine congruence action is
$$ a\star g=g+2a\pmod4, $$
with precisely two orbits, $\{0,2\}$ and $\{1,3\}$.

Therefore $\{0,2\}\subseteq S$ is a **complete good orbit**, but the other orbit is only partially good ($1\in S,\ 3\notin S$).

## Verified consequences

- [`hasCompleteGoodOrbit`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean) verifies that the first orbit is good.
- [`notCongruenceSaturated`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean) proves failure of global saturation.
- [`nontrivialEffectiveGroup`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean) rules out the exceptional trivial-$G$ case.
- [`relationalDLF`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean) proves existence of a countable homogeneous full-age original-relational DLF model.
- [`notRelationalCoherentEPPA`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean) proves that coherent EPPA **fails** for that same original `E,R_c` finite class.
- [`semiCoherentDLFNotCoherent`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourSemiCoherentSeparation.lean) packages **unrestricted raw semi-coherent EP + relational DLF + failure of original-relational coherent EPPA**. By [`finiteRelationalSemiCoherentEP_iff_raw`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/NativeRelationalSemiCoherentConverse.lean), the first conjunct is equivalent to the original-relational property. Ordinary EPPA holds by the unconditional EPPA theorem for all finite data.

The same three properties are now explicitly packaged in the **native original-relational API**, as [`FourColourSeparation.nativeSemiCoherentDLFNotCoherent`](https://github.com/shulda/lean_eppa_semigeneric/blob/e094e5c094de1909df70ef8267258e2d92c3f49b/SemigenericEPPA/Examples/FourColourNativeSemiCoherentSeparation.lean), certified in [PR #601](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40349653163). This is an exact transport of the original certified raw property, not a stronger assumption.

Thus **semi-coherent EP is strictly weaker than coherent EPPA** already for a finite binary equivalence-and-colour Fraïssé age. Likewise DLF of the full automorphism group does *not* imply coherent EPPA.

**Semantic qualification:** the countable model with DLF is a real existential Lean witness. Calling it *the* Fraïssé limit uses the usual mathematical uniqueness theorem, not an additional Lean identification in this project.

See [Main theorems](Main-theorems.md) for both classification equivalences.
