import SemigenericEPPA.Algebra.AffineResidualCode

/-!
# The globally typed raw encoder of an affine residual code

An AffineResidualCode has typed sections
    encode_g : C_g → L.
The fixed-cover orbit-colouring proofs require a plain function
    encodeRaw : C → L
that no longer mentions an effective fibre proof.

Choosing the section at the exact effective image phi(c) gives such
a function. By proof-irrelevance of the fibre predicates, its value
is independent of any alternative equality phi(c)=g.

Crucially, the *global* encoder respects the original affine
reversal equation, so invariant raw edge colours can be converted
to invariant residual matrices without dependent-type coercions.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {d : RawDatum G C}

namespace AffineResidualCode

/-- Encode a raw colour using its canonical exact effective fibre. -/
def encodeRaw (code : AffineResidualCode d L) (c : C) : L :=
  code.encode (d.phi c) ⟨c, rfl⟩

/-- Section encodings at an equality-compatible effective index
coincide with the global raw encoding; the equality proof itself
does not affect the value. -/
theorem encode_of_projection
    (code : AffineResidualCode d L)
    (c : C) (g : G) (hg : d.phi c = g) :
    code.encode g ⟨c, hg⟩ = code.encodeRaw c := by
  cases hg
  rfl

/-- Exact global affine-reversal identity, with no assumptions
about fixed points of s or the raw involution. -/
theorem encodeRaw_reverse
    (code : AffineResidualCode d L) (c : C) :
    code.encodeRaw (d.reverse c) =
      code.shift (d.phi c) - code.encodeRaw c := by
  calc
    code.encodeRaw (d.reverse c) =
      code.encode (d.s (d.phi c))
        ⟨d.reverse c, d.equivariant c⟩ := by
          exact (code.encode_of_projection (d.reverse c)
            (d.s (d.phi c)) (d.equivariant c)).symm
    _ = code.encode (d.s (d.phi c))
        (d.reverseFibre (d.phi c) ⟨c, rfl⟩) := rfl
    _ = code.shift (d.phi c) - code.encodeRaw c :=
      code.encode_reverse (d.phi c) ⟨c, rfl⟩

end AffineResidualCode

end SemigenericEPPA
