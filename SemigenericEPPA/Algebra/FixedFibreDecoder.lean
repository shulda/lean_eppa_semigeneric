import SemigenericEPPA.Algebra.InvolutionRetraction
import SemigenericEPPA.Algebra.AffineResidualCode
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Abel

/-!
# Decoding a self-reversed effective raw fibre

Fix g with s(g)=g. The raw fibre C_g has a genuine involution
c↦c*, while an additive group L has the affine involution
l↦shift(g)-l.

If an encoder C→L is injective and reversal-equivariant, and if
any fixed point of the affine involution forces a self-reversing
raw colour in C_g, then the generic involution-retraction theorem
gives a decoder pi_g:L→C_g which is a left inverse of the encoder
and respects reversal everywhere.

This is the difficult one-fibre step in the finite residual-code
construction. It works whether the raw reversal has fixed points
or is fixed-point-free. The global encoder and its special shift
will provide these assumptions in the universal R0 construction;
nonfixed two-element orbits {g,s(g)} are treated separately.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]

/-- Fibre-local raw reversal when the effective colour g is fixed
by s; unlike generic reverseFibre, its domain and codomain coincide. -/
def RawDatum.fixedFibreReverse (d : RawDatum G C)
    (g : G) (hg : d.s g = g) :
    d.fibre g → d.fibre g :=
  fun c => ⟨d.reverse c.val, by
    rw [d.equivariant, c.property, hg]⟩

/-- Reversal inside a fixed effective fibre is involutive. -/
theorem RawDatum.fixedFibreReverse_involutive
    (d : RawDatum G C) (g : G) (hg : d.s g = g) :
    Function.Involutive (d.fixedFibreReverse g hg) := by
  intro c
  apply Subtype.ext
  exact d.reverse_involutive c.val

/-- An injective, reversal-equivariant raw encoder into any FINITE
additive coefficient group admits a correct decoder on every
s-fixed effective colour g for which affine fixed points can be
decoded by raw fixed colours. The same decoder recovers all old
raw labels and satisfies equation (3.20) literally.

The proof chooses a linear order on the finite coefficient group;
the order is auxiliary and is not introduced into the raw language. -/
theorem exists_fixedFibreAffineDecoder
    [Finite L]
    (d : RawDatum G C)
    (g : G) (hg : d.s g = g)
    (shift : G → L)
    (encode : C → L)
    (hinj : Function.Injective encode)
    (hequiv : ∀ c : C,
      encode (d.reverse c) = shift (d.phi c) - encode c)
    (hfree : g ∉ d.selfReverseEffective →
      ∀ l : L, shift g - l ≠ l) :
    ∃ decode : L → d.fibre g,
      (∀ c : d.fibre g, decode (encode c.val) = c) ∧
      (∀ l : L,
        decode (shift g - l) =
          d.fixedFibreReverse g hg (decode l)) := by
  classical
  letI : Fintype L := Fintype.ofFinite _
  letI : LinearOrder L :=
    LinearOrder.lift' (Fintype.equivFin L)
      (Fintype.equivFin L).injective
  letI : Nonempty (d.fibre g) :=
    ⟨⟨Classical.choose (d.phi_surjective g),
      Classical.choose_spec (d.phi_surjective g)⟩⟩
  let rL : L → L := fun l => shift g - l
  let rC : d.fibre g → d.fibre g := d.fixedFibreReverse g hg
  let e : d.fibre g → L := fun c => encode c.val
  have hrL : Function.Involutive rL := by
    intro l
    change shift g - (shift g - l) = l
    abel
  have hrC : Function.Involutive rC :=
    d.fixedFibreReverse_involutive g hg
  have he : Function.Injective e := by
    intro c c' hcc'
    apply Subtype.ext
    exact hinj hcc'
  have heq : ∀ c : d.fibre g, e (rC c) = rL (e c) := by
    intro c
    change encode (d.reverse c.val) = shift g - encode c.val
    calc
      encode (d.reverse c.val) =
        shift (d.phi c.val) - encode c.val := hequiv c.val
      _ = shift g - encode c.val := by rw [c.property]
  have hfixed :
      (∃ l : L, rL l = l) →
      ∃ c : d.fibre g, rC c = c := by
    rintro ⟨l, hl⟩
    by_cases hs : g ∈ d.selfReverseEffective
    · obtain ⟨c, hc, hrev⟩ := hs
      refine ⟨⟨c, hc⟩, ?_⟩
      apply Subtype.ext
      exact hrev
    · exact False.elim (hfree hs l hl)
  obtain ⟨decode, hsection, hreverse⟩ :=
    exists_equivariantInvolutionRetraction
      rL hrL rC hrC e he heq hfixed
  exact ⟨decode, hsection, hreverse⟩

end SemigenericEPPA
