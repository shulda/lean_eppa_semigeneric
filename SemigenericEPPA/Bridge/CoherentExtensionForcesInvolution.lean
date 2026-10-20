import SemigenericEPPA.Bridge.CoherentEPPA
import AllThoseEPPA.EPPA

/-!
# Coherence forces true involutions from exact partial transpositions

The negative coherent-EPPA obstruction requires the extension of
a partial old transposition to be an actual order-two automorphism
on the WHOLE witness, not just a permutation extending it once.

We isolate the generic upstream reason: an idempotent arrow r
with CoherentTriple r r r extends to an idempotent total
automorphism, hence to the identity because total automorphisms
are injective. If CoherentTriple p p r also holds, the total
extension of p is therefore an involution at EVERY witness point.

This statement uses the actual AllThoseEPPA CoherentExtension,
not a made-up partial semigroup with shrinking domains. The
construction of the concrete old partial transposition r,p and
its three-vertex orbit obstruction is handled separately.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable (act : L.Action Γ)
variable {V : Type w} {W : Type z}
variable {A : Structure L V} {B : Structure L W}
variable {ψ : Structure.Embedding act A B}

/-- Every total upstream automorphism is injective on vertices,
because its underlying partial equivalence has full source. -/
theorem typedAutomorphism_injective
    (g : Structure.Automorphism act B) :
    Function.Injective (fun x : W => g x) := by
  intro x y hxy
  have hx : x ∈ g.toPartialIsomorphism.source := by
    rw [g.source_eq_univ]
    trivial
  have hy : y ∈ g.toPartialIsomorphism.source := by
    rw [g.source_eq_univ]
    trivial
  calc
    x = g.toPartialIsomorphism.toPartialEquiv.symm (g x) :=
      (g.toPartialIsomorphism.toPartialEquiv.left_inv hx).symm
    _ = g.toPartialIsomorphism.toPartialEquiv.symm (g y) :=
      congrArg g.toPartialIsomorphism.toPartialEquiv.symm hxy
    _ = y := g.toPartialIsomorphism.toPartialEquiv.left_inv hy

/-- The extension of an idempotent EXACT partial arrow fixes
the entire ambient witness, not merely its original old domain. -/
theorem coherentExtension_idempotent_fixes_all
    (e : Structure.CoherentExtension act ψ)
    (r : Structure.PartialAutomorphism act A)
    (hrr : Structure.PartialIsomorphism.CoherentTriple r r r)
    (x : W) :
    e.extension r x = x := by
  have hg := e.coherent r r r hrr
  have hpoint : e.extension r x =
      e.extension r (e.extension r x) :=
    congrArg (fun g : Structure.Automorphism act B => g x) hg
  exact (typedAutomorphism_injective act (e.extension r) hpoint).symm

/-- The extension of an involutive old exact partial automorphism
p is a TRUE total involution, if its square is equivalent to
an idempotent old arrow r and coherence is available. -/
theorem coherentExtension_partialInvolution
    (e : Structure.CoherentExtension act ψ)
    (p r : Structure.PartialAutomorphism act A)
    (hrr : Structure.PartialIsomorphism.CoherentTriple r r r)
    (hpp : Structure.PartialIsomorphism.CoherentTriple p p r)
    (x : W) :
    e.extension p (e.extension p x) = x := by
  have h := congrArg
    (fun g : Structure.Automorphism act B => g x)
    (e.coherent p p r hpp)
  calc
    e.extension p (e.extension p x) = e.extension r x := h.symm
    _ = x := coherentExtension_idempotent_fixes_all act e r hrr x

end SemigenericEPPA
