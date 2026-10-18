import SemigenericEPPA.Algebra.RawDatum
import SemigenericEPPA.Algebra.ResidualBaseline
import Mathlib.Tactic.Abel

/-!
# Uniform affine residual codes: precise R0/R1 interface

The manuscript uses one finite abelian group L_O for each orbit O
of the effective reversal s on G. A finite product of those L_O
is a convenient common coefficient group L for *all* fibres:
the affine shift t(g) is supported on the factor of O(g), and
the decoding map at g reads only this factor.

We therefore expose the following single-group interface:
* affine reversal rho_g(l) = t(g) - l, t(s(g)) = t(g);
* an actual decoder into the *typed* raw fibre C_g;
* a section of the decoder;
* both reversal identities (3.20), for decoder and section.

This file checks the algebra and typing only. The existence of
such a finite code for each finite raw datum is NOT assumed or
asserted here; that is the forthcoming R0 finite coding theorem.
This interface permits the R1 raw cover to be formalized without
dependent group-valued coordinate types.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]

namespace RawDatum

/-- Raw colours in the exact fibre over effective colour g. -/
def fibre (d : RawDatum G C) (g : G) : Type v :=
  {c : C // d.phi c = g}

/-- Reversal is an actual map of the appropriately typed fibres,
including when s(g) is not g. -/
def reverseFibre (d : RawDatum G C) (g : G)
    (c : d.fibre g) : d.fibre (d.s g) :=
  ⟨d.reverse c.val, by
    rw [d.equivariant, c.property]⟩

@[simp] theorem reverseFibre_val (d : RawDatum G C)
    (g : G) (c : d.fibre g) :
    (d.reverseFibre g c).val = d.reverse c.val := rfl

end RawDatum

/-- A group-valued scratch space resolving every raw fibre by one
common finite abelian coefficient group. The group need only be
finite for the eventual *finite cover* theorem, not for this algebra.

The two exact equations are the manuscript's (3.20), with the
appropriate raw fibre subtype equality retained rather than
discarded. -/
structure AffineResidualCode
    (d : RawDatum G C) (L : Type w) [AddCommGroup L] where
  shift : G → L
  shift_reverse : ∀ g : G, shift (d.s g) = shift g
  decode : ∀ g : G, L → d.fibre g
  encode : ∀ g : G, d.fibre g → L
  decode_encode : ∀ g : G, ∀ c : d.fibre g,
    decode g (encode g c) = c
  decode_reverse : ∀ g : G, ∀ l : L,
    decode (d.s g) (shift g - l) =
      d.reverseFibre g (decode g l)
  encode_reverse : ∀ g : G, ∀ c : d.fibre g,
    encode (d.s g) (d.reverseFibre g c) =
      shift g - encode g c

namespace AffineResidualCode

variable {d : RawDatum G C}
variable (code : AffineResidualCode d L)

/-- The residual reversal over an effective colour g is affine. -/
def reverseAt (g : G) (l : L) : L := code.shift g - l

/-- Reverse twice (first over g and then over s(g)) is literally
the identity, even with a nonzero affine shift. -/
theorem reverseAt_involutive (g : G) (l : L) :
    code.reverseAt (d.s g) (code.reverseAt g l) = l := by
  simp only [reverseAt, code.shift_reverse]
  abel

/-- Every decoder preserves its effective colour exactly. -/
theorem decode_phi (g : G) (l : L) :
    d.phi (code.decode g l).val = g :=
  (code.decode g l).property

/-- Every decoder is surjective onto the actual fibre, with the
explicit section supplied by the code. -/
theorem decode_surjective (g : G) :
    Function.Surjective (code.decode g) := by
  intro c
  exact ⟨code.encode g c, code.decode_encode g c⟩

/-- Exact reversal of the decoded raw colour, equation (3.20). -/
theorem decode_reverse_val (g : G) (l : L) :
    (code.decode (d.s g) (code.reverseAt g l)).val =
      d.reverse (code.decode g l).val := by
  exact congrArg Subtype.val (code.decode_reverse g l)

/-- Exact reversal of the encoded old raw colour (3.20). -/
theorem encode_reverse_eq (g : G) (c : d.fibre g) :
    code.encode (d.s g) (d.reverseFibre g c) =
      code.reverseAt g (code.encode g c) :=
  code.encode_reverse g c

end AffineResidualCode

end SemigenericEPPA
