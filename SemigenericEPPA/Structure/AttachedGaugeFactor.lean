import SemigenericEPPA.Structure.OnePointEffective
import SemigenericEPPA.Structure.QuotientGaugeConverse

/-!
# Side-preserving gauge formula for an attached new vertex

Let D be an effective E-rectangle geometry and L an actual one-point
extension. If the new vertex belongs to the old E-class of p, then
for another old part with anchor q and every a E q, the new→old edge
is reconstructed from the *reverse* one-point edge q→new by

  L.F(new,a) = s(L.F(q,new)) * D.F(p,q)⁻¹ * D.F(p,a).

This is the exact noncommutative gauge-coordinate identity needed for
the attached-new/old preservation branch of the global SAP construction.
It follows from the actual R3 law of L; no extra colour/gauge choices
or assumptions about self-reversing colours are introduced.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- An attached new vertex has precisely the affine gauge factorization
towards a different old E-class, with the reverse edge in the left
coordinate and in the manuscript's noncommutative factor order. -/
theorem onePoint_attached_new_to_old_formula
    (D : EffectiveGeometry s V)
    (L : OnePointEffectiveExtension D)
    (p q a : V)
    (hnewp : L.geometry.part none (some p))
    (hqa : D.part q a)
    (hpq : ¬D.part p q) :
    L.geometry.F none (some a) =
      s (L.geometry.F (some q) none) *
        (D.F p q)⁻¹ * D.F p a := by
  have hqy : L.geometry.part (some q) (some a) :=
    (L.old_part q a).2 hqa
  have hcross : ¬L.geometry.part none (some q) := by
    intro hnewq
    have hpq' : L.geometry.part (some p) (some q) :=
      L.geometry.part.iseqv.trans
        (L.geometry.part.iseqv.symm hnewp) hnewq
    exact hpq ((L.old_part p q).1 hpq')
  have hfact := L.geometry.anchored_factor
    none (some p) (some q) (some a)
    hnewp hqy hcross
  rw [L.old_F p q, L.old_F p a] at hfact
  have hreverse :
      s (L.geometry.F (some q) none) =
        L.geometry.F none (some q) := by
    rw [L.geometry.reverse_cross none (some q) hcross, s.involutive]
  calc
    L.geometry.F none (some a) =
      L.geometry.F none (some q) *
        (D.F p q)⁻¹ * D.F p a := hfact
    _ = s (L.geometry.F (some q) none) *
        (D.F p q)⁻¹ * D.F p a := by rw [hreverse]

/-- Old representatives may be replaced within their E-classes
without changing the reconstructed new→old effective colour. -/
theorem onePoint_attached_new_to_old_formula_unanchored
    (D : EffectiveGeometry s V)
    (L : OnePointEffectiveExtension D)
    (p p' q a : V)
    (hnewp : L.geometry.part none (some p))
    (hpp' : D.part p p')
    (hqa : D.part q a)
    (hpq : ¬D.part p q) :
    L.geometry.F none (some a) =
      s (L.geometry.F (some q) none) *
        (D.F p' q)⁻¹ * D.F p' a := by
  have hnewp' : L.geometry.part none (some p') :=
    L.geometry.part.iseqv.trans hnewp
      ((L.old_part p p').2 hpp')
  have hp'q : ¬D.part p' q := by
    intro hp'q
    exact hpq (D.part.iseqv.trans hpp' hp'q)
  exact onePoint_attached_new_to_old_formula
    D L p' q a hnewp' hqa hp'q

end SemigenericEPPA
