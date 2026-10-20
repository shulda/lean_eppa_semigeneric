import SemigenericEPPA.Bridge.UpstreamExactArrowFunctoriality
import SemigenericEPPA.Bridge.RawAutomorphismSubgroupTyped
import SemigenericEPPA.Bridge.RawTypedEmbedding
import AllThoseEPPA.EPPA

/-!
# Final API conversion: a genuine exact raw groupoid functor is typed coherent EPPA

Let P be a literal old raw rectangle presentation, Q a literal
whole-witness raw rectangle presentation and psi:P↪Q one fixed
induced old embedding.

Suppose the EXACT groupoid of partial raw isomorphisms between
induced subsets S,T of P is assigned one actual whole-witness
raw automorphism F(S,T,f) of Q, respecting exact composition and
extending each old arrow f on the fixed embedded old vertices.

No additional independent choices are needed for upstream
AllThoseEPPA CoherentExtension. PartialEquiv.Equivalent means
the same exact S,T,f (proved in UpstreamExactArrowFunctoriality),
and CoherentTriple is precisely exact source/target-matched
composition. The full witness automorphism subgroup is converted
to the original typed relational language by the already certified
strict identity/multiplication converter.

Consequently a single such raw functor immediately gives the
unconditional typed coherent-EPPA WITNESS predicate (conditional
only on the functor itself). The positive G=1 construction must
supply that functor using the component/stabilizer machinery.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t
variable {G : Type u} [Group G]
variable {C : Type v} {A : Type w} {W : Type z}
variable {d : RawDatum G C}
variable {K : Type t} [Group K]

namespace RawRectanglePresentation

/-- Extensionality of functor values under exact source/target
equalities and heterogeneous equality of old raw arrows. The
equalities are eliminated only for ABSTRACT subset variables,
never by destructing source/target projections of PartialEquiv. -/
private theorem rawFunctor_heq_congr
    (P : RawRectanglePresentation d A)
    (F : (S T : Set A) → ExactPartialIso P S T → K)
    {S S' T T' : Set A}
    (hS : S = S') (hT : T = T')
    (f : ExactPartialIso P S T)
    (g : ExactPartialIso P S' T')
    (hfg : HEq f g) :
    F S T f = F S' T' g := by
  cases hS
  cases hT
  exact congrArg (F S T) (eq_of_heq hfg)

/-- Composition of F with an exact old arrow whose target is
transported to the next arrow's source. Rewriting an abstract
set equality here avoids dependent elimination of upstream
PartialEquiv source/target projections. -/
private theorem rawFunctor_comp_cast
    (P : RawRectanglePresentation d A)
    (F : (S T : Set A) → ExactPartialIso P S T → K)
    (hComp : ∀ (S T U : Set A)
      (f : ExactPartialIso P S T) (g : ExactPartialIso P T U),
      F S U (g.comp f) = F T U g * F S T f)
    {S T T' U : Set A} (h : T = T')
    (f : ExactPartialIso P S T)
    (g : ExactPartialIso P T' U) :
    F S U (g.comp (h ▸ f)) = F T' U g * F S T f := by
  cases h
  exact hComp S T U f g

/-- Any exact groupoid functor automatically ignores irrelevant
off-domain values of upstream PartialEquiv representations. -/
theorem rawFunctor_respectsUpstreamEquivalent
    (P : RawRectanglePresentation d A)
    (F : (S T : Set A) → ExactPartialIso P S T → K)
    (p q : Structure.PartialAutomorphism
      (rectangleTrivialAction C) P.toStructure)
    (h : Structure.PartialIsomorphism.Equivalent p q) :
    F p.source p.target (P.upstreamToExactRawArrow p) =
      F q.source q.target (P.upstreamToExactRawArrow q) := by
  obtain ⟨hs, ht, _⟩ :=
    P.upstreamEquivalent_exactSourceTarget p q h
  exact rawFunctor_heq_congr P F hs ht
    (P.upstreamToExactRawArrow p)
    (P.upstreamToExactRawArrow q)
    (P.upstreamToExactRawArrow_equivalent p q h)

/-- Exact composition law in the old raw groupoid is precisely
the upstream CoherentTriple equation after quotienting away
irrelevant off-domain values of PartialEquiv. -/
theorem rawFunctor_respectsUpstreamCoherentTriple
    (P : RawRectanglePresentation d A)
    (F : (S T : Set A) → ExactPartialIso P S T → K)
    (hComp : ∀ (S T U : Set A)
      (f : ExactPartialIso P S T) (g : ExactPartialIso P T U),
      F S U (g.comp f) = F T U g * F S T f)
    (f g h : Structure.PartialAutomorphism
      (rectangleTrivialAction C) P.toStructure)
    (hTriple : Structure.PartialIsomorphism.CoherentTriple f g h) :
    F h.source h.target (P.upstreamToExactRawArrow h) =
      F g.source g.target (P.upstreamToExactRawArrow g) *
        F f.source f.target (P.upstreamToExactRawArrow f) := by
  obtain ⟨htg, hEquivalent⟩ := hTriple
  have hArrow :
      HEq (P.upstreamToExactRawArrow (g.comp f htg))
        ((P.upstreamToExactRawArrow g).comp
          (htg ▸ P.upstreamToExactRawArrow f)) :=
    P.upstreamToExactRawArrow_comp f g htg
  calc
    F h.source h.target (P.upstreamToExactRawArrow h) =
      F (g.comp f htg).source (g.comp f htg).target
        (P.upstreamToExactRawArrow (g.comp f htg)) :=
          P.rawFunctor_respectsUpstreamEquivalent F
            h (g.comp f htg) hEquivalent
    _ = F f.source g.target
          ((P.upstreamToExactRawArrow g).comp
            (htg ▸ P.upstreamToExactRawArrow f)) := by
      change F f.source g.target
        (P.upstreamToExactRawArrow (g.comp f htg)) = _
      exact congrArg (F f.source g.target) (eq_of_heq hArrow)
    _ = F g.source g.target (P.upstreamToExactRawArrow g) *
          F f.source f.target (P.upstreamToExactRawArrow f) :=
      rawFunctor_comp_cast P F hComp htg
        (P.upstreamToExactRawArrow f)
        (P.upstreamToExactRawArrow g)

/-- If the original old P admits ONE genuine coherent functor
of exact induced raw arrows into the true automorphism subgroup
of one finite raw witness Q, that SAME witness is an upstream
typed CoherentEPPAWitness in the original R1--R3 language. -/
theorem coherentTypedEPPA_of_exactRawFunctor
    (P : RawRectanglePresentation d A)
    (Q : RawRectanglePresentation d W)
    (psi : A → W)
    (hInj : Function.Injective psi)
    (hPart : ∀ x y, Q.part (psi x) (psi y) ↔ P.part x y)
    (hColour : ∀ x y, Q.colour (psi x) (psi y) = P.colour x y)
    (F : (S T : Set A) → ExactPartialIso P S T →
      Q.actualRawAutomorphismGroup)
    (hFcomp : ∀ (S T U : Set A)
      (f : ExactPartialIso P S T) (g : ExactPartialIso P T U),
      F S U (g.comp f) = F T U g * F S T f)
    (hFext : ∀ (S T : Set A)
      (f : ExactPartialIso P S T) (x : S),
      (F S T f).val (psi x.val) = psi (f.toEquiv x).val) :
    ∃ psityped : Structure.Embedding
        (rectangleTrivialAction C) P.toStructure Q.toStructure,
      Structure.IsCoherentEPPAWitness
        (rectangleTrivialAction C) psityped := by
  let psityped : Structure.Embedding
      (rectangleTrivialAction C) P.toStructure Q.toStructure :=
    P.toTypedEmbedding Q psi hInj hPart hColour
  let extension (p : Structure.PartialAutomorphism
      (rectangleTrivialAction C) P.toStructure) :
      Structure.Automorphism (rectangleTrivialAction C) Q.toStructure :=
    Q.actualRawAutomorphism_toTyped
      (F p.source p.target (P.upstreamToExactRawArrow p))
  refine ⟨psityped, ⟨{
    extension := extension
    extension_spec := ?_
    respects_equivalent := ?_
    coherent := ?_
  }⟩⟩
  · intro p
    constructor
    · have hlang : p.lang = (1 : Equiv.Perm (Fin 0)) := by
        apply Equiv.ext
        intro i
        exact Fin.elim0 i
      change (1 : Equiv.Perm (Fin 0)) * 1 = 1 * p.lang
      simp [hlang]
    · intro x hx
      change (F p.source p.target
        (P.upstreamToExactRawArrow p)).val (psi x) = psi (p x)
      have hEndpoint :
          ((P.upstreamToExactRawArrow p).toEquiv
            (⟨x, hx⟩ : p.source)).val = p x := rfl
      calc
        (F p.source p.target
          (P.upstreamToExactRawArrow p)).val (psi x) =
            psi ((P.upstreamToExactRawArrow p).toEquiv
              (⟨x, hx⟩ : p.source)).val :=
                hFext p.source p.target
                  (P.upstreamToExactRawArrow p) ⟨x, hx⟩
        _ = psi (p x) := congrArg psi hEndpoint
  · intro p q heq
    change Q.actualRawAutomorphism_toTyped
      (F p.source p.target (P.upstreamToExactRawArrow p)) =
      Q.actualRawAutomorphism_toTyped
        (F q.source q.target (P.upstreamToExactRawArrow q))
    rw [P.rawFunctor_respectsUpstreamEquivalent F p q heq]
  · intro f g h htriple
    change Q.actualRawAutomorphism_toTyped
      (F h.source h.target (P.upstreamToExactRawArrow h)) =
      (Q.actualRawAutomorphism_toTyped
        (F g.source g.target (P.upstreamToExactRawArrow g))).comp
        (Q.actualRawAutomorphism_toTyped
          (F f.source f.target (P.upstreamToExactRawArrow f)))
    rw [P.rawFunctor_respectsUpstreamCoherentTriple
      F hFcomp f g h htriple]
    exact Q.actualRawAutomorphism_toTyped_mul
      (F g.source g.target (P.upstreamToExactRawArrow g))
      (F f.source f.target (P.upstreamToExactRawArrow f))

end RawRectanglePresentation

end SemigenericEPPA
