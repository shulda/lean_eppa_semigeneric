import SemigenericEPPA.Valuations.TransportEquiv
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod

/-!
# Finiteness of the complete two-layer effective EPPA witness

The effective witness has two valuation sorts:
* witness parts (i,h), with i an E-class and h : V → G;
* witness vertices (q,x,χ), where x belongs to i and χ has a
  coordinate toward each witness part different from q.

For finite old V and finite group G, BOTH witness sorts are finite.
The vertex proof uses the verified dependent-sum equivalence, so it
counts every valuation coordinate and respects all membership data.
Empty V and parts of different sizes are allowed.

This is the finiteness component of an EPPA witness. Extending old
partial automorphisms and selecting raw fibre colours remain separate.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

variable (D : EffectiveGeometry s V)

/-- A concrete Fintype on the part valuation sort
(V/E) × (V → G), for finite old V and finite G. -/
noncomputable def fintypeEffectiveWitnessParts
    [Fintype V] [Fintype G] :
    Fintype (EffectiveWitnessPart D) := by
  classical
  letI : Fintype (Quotient D.part) := Fintype.ofFinite _
  infer_instance

/-- An actual enumeration of the whole witness vertex sort, using the
dependent sum over its witness part, its exact old-label fibre,
and its independent group-valued vertex valuation coordinates. -/
noncomputable def fintypeEffectiveWitnessVertices
    [Fintype V] [Fintype G] :
    Fintype (EffectiveWitnessVertex D) := by
  classical
  letI : Fintype (EffectiveWitnessPart D) :=
    D.fintypeEffectiveWitnessParts
  have hfib :
      ∀ q : EffectiveWitnessPart D,
        Fintype (EffectiveWitnessFibreData D q) := by
    intro q
    infer_instance
  letI : ∀ q : EffectiveWitnessPart D,
      Fintype (EffectiveWitnessFibreData D q) := hfib
  exact Fintype.ofEquiv
    (Σ q : EffectiveWitnessPart D, EffectiveWitnessFibreData D q)
    (witnessVertexSigmaEquiv D).symm

/-- Finite, not necessarily explicitly enumerated old vertices and
group elements imply a finite witness-part sort. -/
theorem finite_effectiveWitnessParts
    [Finite V] [Finite G] :
    Finite (EffectiveWitnessPart D) := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype G := Fintype.ofFinite _
  letI : Fintype (EffectiveWitnessPart D) :=
    D.fintypeEffectiveWitnessParts
  infer_instance

/-- Finite, not necessarily explicitly enumerated old vertices and
group elements imply a finite *full* two-layer witness vertex sort.
No normalized affine reversal, nonemptiness, or equal-size-part
assumption is required for finiteness. -/
theorem finite_effectiveWitnessVertices
    [Finite V] [Finite G] :
    Finite (EffectiveWitnessVertex D) := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype G := Fintype.ofFinite _
  letI : Fintype (EffectiveWitnessVertex D) :=
    D.fintypeEffectiveWitnessVertices
  infer_instance

end EffectiveGeometry

end SemigenericEPPA
