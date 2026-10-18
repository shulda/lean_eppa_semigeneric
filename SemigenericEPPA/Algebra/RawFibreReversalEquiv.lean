import SemigenericEPPA.Algebra.AffineResidualCode

/-!
# Equivalence of raw fibres under reversal

Every raw-colour fibre C_g is canonically equivalent to C_{s(g)}
through the raw-colour reversal involution. The two fibres need
not be definitionally the same type, even when s(s(g))=g.

This small typed equivalence is the exact transport needed to
apply the abstract paired-decoder theorem to effective reversal
orbits of size two, without silently coalescing distinct fibres
or weakening the raw colour equality to its effective projection.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

/-- Raw reversal is a genuine equivalence between the exact
g- and s(g)-fibres, with inverse given by raw reversal again. -/
def RawDatum.reverseFibreEquiv (d : RawDatum G C)
    (g : G) : d.fibre g ≃ d.fibre (d.s g) where
  toFun := d.reverseFibre g
  invFun := fun c =>
    ⟨d.reverse c.val, by
      calc
        d.phi (d.reverse c.val) = d.s (d.phi c.val) :=
          d.equivariant c.val
        _ = d.s (d.s g) := congrArg d.s c.property
        _ = g := d.s.involutive g⟩
  left_inv := by
    intro c
    apply Subtype.ext
    exact d.reverse_involutive c.val
  right_inv := by
    intro c
    apply Subtype.ext
    exact d.reverse_involutive c.val

@[simp] theorem RawDatum.reverseFibreEquiv_val
    (d : RawDatum G C) (g : G) (c : d.fibre g) :
    (d.reverseFibreEquiv g c).val = d.reverse c.val := rfl

@[simp] theorem RawDatum.reverseFibreEquiv_symm_val
    (d : RawDatum G C) (g : G) (c : d.fibre (d.s g)) :
    ((d.reverseFibreEquiv g).symm c).val =
      d.reverse c.val := rfl

end SemigenericEPPA
