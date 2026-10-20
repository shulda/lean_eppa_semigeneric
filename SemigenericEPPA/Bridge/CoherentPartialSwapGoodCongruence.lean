import SemigenericEPPA.Bridge.TypedInvolutionGoodCongruence
import SemigenericEPPA.Bridge.CoherentClosedSubsetInvolution
import SemigenericEPPA.Bridge.RawTypedEmbedding

/-!
# Coherence of an old partial transposition forces a good congruence colour

We combine the two genuinely certified mechanisms in the necessary
direction of the coherent-EPPA classification:

1. In the exact upstream PartialEquiv groupoid, coherence forces the
   whole-witness extension of a closed old involutive partial arrow
   p:S→S to be an actual total involution of its witness.
2. The image of the old cross-E transposition u↔z under that total
   involution, together with the third old vertex v E u, creates
   the missing vertex w=T(v) and an actual raw rectangle. Its
   fourth effective colour is a⋆g and is self-reversing.

The old source is a literal R1--R3 structure, the witness is a
literal R1--R3 raw structure, and the embedding and coherent
extension have the exact upstream AllThoseEPPA types.
No raw permutation or additional witness action is assumed.

A later specialization to the three-vertex 2+1 old gadget makes
the required partial transposition for every g∈S and every a∈G,
and obtains the global congruence-saturation obstruction.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w} {W : Type z}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- An old exact partial transposition p swapping u,z, together
with the third old vertex v in u's E-part, forces every chosen
congruence colour a⋆g to have a genuine self-reversing raw
representative in any coherent witness. The old effective entries
are restated in the witness after embedding; their transfer from
P follows from literal raw-colour preservation. -/
theorem goodCongruence_of_coherentPartialTransposition
    (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W)
    (psi : Structure.Embedding
      (rectangleTrivialAction C) P.toStructure Q.toStructure)
    (e : Structure.CoherentExtension (rectangleTrivialAction C) psi)
    (p : Structure.PartialAutomorphism
      (rectangleTrivialAction C) P.toStructure)
    (S : Set V) (hS : P.toStructure.IsClosed S)
    (hSource : p.source = S) (hTarget : p.target = S)
    (hLang : p.lang * p.lang = 1)
    (hSquare : ∀ x : V, x ∈ S → p (p x) = x)
    (u v z : V)
    (hu : u ∈ S) (hz : z ∈ S)
    (hSwapUZ : p u = z) (hSwapZU : p z = u)
    (huv : P.part u v)
    (huz : ¬P.part u z)
    (a g : G) (hg : d.s g = g)
    (huzg : Q.effectiveReduct.F (psi u) (psi z) = g)
    (hvza : Q.effectiveReduct.F (psi v) (psi z) = a * g) :
    congruence d.s a g ∈ d.selfReverseEffective := by
  have hpsiLang : psi.lang = (1 : Equiv.Perm (Fin 0)) := by
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  have hpsiPart (x y : V) :
      Q.part (psi x) (psi y) ↔ P.part x y := by
    have h := psi.map_rel_iff
      (binarySymbol C none) (pairTuple x y)
    rw [hpsiLang, Language.Action.onRel_one] at h
    change Q.part (psi x) (psi y) ↔ P.part x y at h
    exact h
  have huvQ : Q.part (psi u) (psi v) :=
    (hpsiPart u v).mpr huv
  have huzQ : ¬Q.part (psi u) (psi z) := by
    intro h
    exact huz ((hpsiPart u z).mp h)
  let T : Structure.Automorphism
      (rectangleTrivialAction C) Q.toStructure := e.extension p
  have hTinv (x : W) : T (T x) = x :=
    coherentExtension_involution_of_squareOnSource
      (rectangleTrivialAction C) e p S hS
      hSource hTarget hLang hSquare x
  have hExtUZ : T (psi u) = psi z := by
    have h := (e.extension_spec p).2 u (hSource.symm ▸ hu)
    change T (psi u) = psi (p u) at h
    rw [hSwapUZ] at h
    exact h
  have hExtZU : T (psi z) = psi u := by
    have h := (e.extension_spec p).2 z (hSource.symm ▸ hz)
    change T (psi z) = psi (p z) at h
    rw [hSwapZU] at h
    exact h
  exact Q.goodCongruence_of_typedInvolution
    T hTinv (psi u) (psi v) (psi z)
    huvQ huzQ hExtUZ hExtZU a g hg huzg hvza

end RawRectanglePresentation

end SemigenericEPPA
