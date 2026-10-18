import SemigenericEPPA.Algebra.PairedInvolutionRetraction
import SemigenericEPPA.Algebra.RawFibreReversalEquiv
import Mathlib.Tactic.Abel

/-!
# Paired affine decoders for a reversal orbit

The nonfixed effective-colour orbit {g,s(g)} admits two compatible
typed decoders, given an injective raw encoder and the exact affine
reversal identity. The abstract paired equivariant retraction and
the raw-fibre equivalence supply their existence immediately.

This theorem does not identify C_g with C_{s(g)} definitionally,
and remains valid even for general noncommutative effective G.
It will be used to select compatible decoders simultaneously
for all nonfixed effective reversal orbits.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]

/-- An injective equivariant raw encoder determines decoders for
both raw fibres over g and s(g), simultaneously left-inverse
and compatible with affine reversal in both directions. -/
theorem exists_pairedFibreAffineDecoders
    (d : RawDatum G C)
    (g : G)
    (shift : G → L)
    (encode : C → L)
    (hinj : Function.Injective encode)
    (hequiv : ∀ c : C,
      encode (d.reverse c) = shift (d.phi c) - encode c) :
    ∃ (q₁ : L → d.fibre g) (q₂ : L → d.fibre (d.s g)),
      (∀ c : d.fibre g, q₁ (encode c.val) = c) ∧
      (∀ c : d.fibre (d.s g), q₂ (encode c.val) = c) ∧
      (∀ l : L,
        q₂ (shift g - l) = d.reverseFibreEquiv g (q₁ l)) ∧
      (∀ l : L,
        q₁ (shift g - l) = (d.reverseFibreEquiv g).symm (q₂ l)) := by
  classical
  letI : Nonempty (d.fibre g) :=
    ⟨⟨Classical.choose (d.phi_surjective g),
      Classical.choose_spec (d.phi_surjective g)⟩⟩
  let τ : L → L := fun l => shift g - l
  have hτ : Function.Involutive τ := by
    intro l
    change shift g - (shift g - l) = l
    abel
  let e₁ : d.fibre g → L := fun c => encode c.val
  let e₂ : d.fibre (d.s g) → L := fun c => encode c.val
  have he₁ : Function.Injective e₁ := by
    intro c c' hcc'
    apply Subtype.ext
    exact hinj hcc'
  have heq : ∀ c : d.fibre g,
      e₂ (d.reverseFibreEquiv g c) = τ (e₁ c) := by
    intro c
    change encode (d.reverse c.val) = shift g - encode c.val
    calc
      encode (d.reverse c.val) =
          shift (d.phi c.val) - encode c.val := hequiv c.val
      _ = shift g - encode c.val := by rw [c.property]
  exact exists_equivariantPairedRetraction
    (d.reverseFibreEquiv g) τ hτ e₁ e₂ he₁ heq

end SemigenericEPPA
