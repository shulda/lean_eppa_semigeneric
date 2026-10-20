import SemigenericEPPA.Bridge.TypedRawEffectiveColourEmbedding
import SemigenericEPPA.Bridge.CoherentPartialSwapGoodCongruence
import SemigenericEPPA.Bridge.TwoPlusOneTypedTransposition
import SemigenericEPPA.Algebra.CongruenceAction

/-!
# The exact 2+1 obstruction proves congruence saturation is necessary

Given a raw self-reversing colour c₀ with effective colour g and
ANY group element a, choose a raw colour c₁ over a*g.
The genuine three-vertex rectangle presentation
  u,v | z
has exact original raw colours c(u,z)=c₀, c(v,z)=c₁.

The original typed partial transposition u↔z on the EXACT
two-vertex induced subset {u,z} is an involution because c₀ is
self-reversing. In ANY true upstream coherent EPPA witness,
coherence forces its extension to be an involution. The geometric
typed 2+1 rectangle obstruction then produces a self-reversing
raw colour above the congruence translate a⋆g.

Crucially the effective colours on the old u–z and v–z edges
inside the witness are obtained from the LITERAL typed embedding;
they are not assumptions. Therefore if all these finite old
structures have coherent witnesses, the set of effective fibres
containing a raw self-reversing colour is congruence-saturated.
This theorem is the necessity/saturation branch of manuscript
Theorem 4.5 and does not assume S is nonempty.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}

/-- A coherent witness of the genuine 2+1 raw gadget forces the
congruence translate of its self-reversing first cross-colour to
be good. No other witness geometry or raw-preservation
hypotheses are required beyond the original typed embedding. -/
theorem RawDatum.goodCongruence_of_twoPlusOneCoherentWitness
    (d : RawDatum G C)
    (c₀ c₁ : C)
    (hfix : d.reverse c₀ = c₀)
    (a : G)
    (hφ₁ : d.phi c₁ = a * d.phi c₀)
    (W : Type w)
    (Q : RawRectanglePresentation d W)
    (ψ : Structure.Embedding (rectangleTrivialAction C)
      (d.twoPlusOneRawPresentation
        (fun b : Bool => if b then c₁ else c₀)).toStructure
      Q.toStructure)
    (hwitness : Structure.IsCoherentEPPAWitness
      (rectangleTrivialAction C) ψ) :
    congruence d.s a (d.phi c₀) ∈ d.selfReverseEffective := by
  classical
  let c : Bool → C := fun b => if b then c₁ else c₀
  let P := d.twoPlusOneRawPresentation c
  have hfix' : d.reverse (c false) = c false := by
    simpa [c] using hfix
  let p := d.twoPlusOneTypedTransposition c hfix'
  obtain ⟨e⟩ := hwitness
  obtain ⟨hsource, htarget, hlang, hsquare⟩ :=
    d.twoPlusOneTypedTransposition_exactSquare c hfix'
  have hclosed : P.toStructure.IsClosed twoPlusOneSwapSource := by
    intro n F xs hx
    exact PEmpty.elim F
  have hu : (some false : Option Bool) ∈ twoPlusOneSwapSource := by
    simp [twoPlusOneSwapSource]
  have hz : (none : Option Bool) ∈ twoPlusOneSwapSource := by
    simp [twoPlusOneSwapSource]
  have hgood : d.s (d.phi c₀) = d.phi c₀ :=
    d.selfReverse_phi_fixed c₀ hfix
  have heffUZ :
      Q.effectiveReduct.F (ψ (some false)) (ψ none) =
        d.phi c₀ := by
    calc
      Q.effectiveReduct.F (ψ (some false)) (ψ none) =
        P.effectiveReduct.F (some false) none :=
          P.effectiveColour_of_typedEmbedding Q ψ
            (some false) none (d.twoPlusOne_cross_uz c)
      _ = d.phi c₀ := by
        simpa [c] using d.twoPlusOne_effective_uz c
  have heffVZ :
      Q.effectiveReduct.F (ψ (some true)) (ψ none) =
        a * d.phi c₀ := by
    calc
      Q.effectiveReduct.F (ψ (some true)) (ψ none) =
        P.effectiveReduct.F (some true) none :=
          P.effectiveColour_of_typedEmbedding Q ψ
            (some true) none (by
              simp [P, RawDatum.twoPlusOneRawPresentation])
      _ = d.phi c₁ := by
        simpa [c] using d.twoPlusOne_effective_vz c
      _ = a * d.phi c₀ := hφ₁
  exact P.goodCongruence_of_coherentPartialTransposition
    Q ψ e p twoPlusOneSwapSource hclosed
    hsource htarget hlang hsquare
    (some false) (some true) none hu hz
    rfl rfl
    (d.twoPlusOne_part_uv c)
    (d.twoPlusOne_cross_uz c)
    a (d.phi c₀) hgood heffUZ heffVZ

/-- If all 2+1 gadgets based at EVERY self-reversing raw colour
admit literal typed coherent witnesses (possibly on different
carriers), the ENTIRE self-reversing effective-colour set is
congruence-saturated. This requires no assumption on G≠1,
finiteness, or existence of an initial self-reversing colour. -/
theorem RawDatum.isCongruenceSaturated_of_twoPlusOneCoherentWitnesses
    (d : RawDatum G C)
    (hwitness :
      ∀ (c : Bool → C)
        (hfix : d.reverse (c false) = c false),
        ∃ (W : Type w)
          (Q : RawRectanglePresentation d W)
          (ψ : Structure.Embedding (rectangleTrivialAction C)
            (d.twoPlusOneRawPresentation c).toStructure
            Q.toStructure),
            Structure.IsCoherentEPPAWitness
              (rectangleTrivialAction C) ψ) :
    d.IsCongruenceSaturated := by
  intro a g hg
  obtain ⟨c₀, hφ₀, hfix⟩ := hg
  obtain ⟨c₁, hφ₁⟩ := d.phi_surjective (a * g)
  let c : Bool → C := fun b => if b then c₁ else c₀
  have hfix' : d.reverse (c false) = c false := by
    simpa [c] using hfix
  obtain ⟨W, Q, ψ, hcoherent⟩ := hwitness c hfix'
  have hφ₁' : d.phi c₁ = a * d.phi c₀ := by
    rw [hφ₀]
    exact hφ₁
  have hgood :=
    d.goodCongruence_of_twoPlusOneCoherentWitness
      c₀ c₁ hfix a hφ₁' W Q ψ hcoherent
  simpa only [hφ₀] using hgood

end SemigenericEPPA
