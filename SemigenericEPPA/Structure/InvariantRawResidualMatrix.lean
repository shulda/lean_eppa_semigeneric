import SemigenericEPPA.Structure.RawCoverPotentialGroupAction
import SemigenericEPPA.Algebra.AffineResidualGlobalEncoder

/-!
# H-invariant affine residual matrices from invariant raw colours

The fixed-cover homomorphic raw lift needs an H-invariant additive
residual matrix r with the correct affine reversal (4.8). This is
immediate once the actual raw colour of every ordered effective
cross-pair is chosen invariantly under H and compatibly with raw
reversal.

An affine raw encoder E:C→L satisfying
    E(c*) = shift(phi(c)) - E(c)
turns the raw colouring c(x,y) into r(x,y)=E(c(x,y)).
Its H-invariance, reversal law and agreement with prescribed old
baselines are then literal identities.

This isolates the geometric orbit-colouring input of #125–#127
from the analytic potential-action construction #121–#124/#128.
No finite raw-cover group action or coherent EPPA statement is
claimed here: those are obtained only after the invariant colouring,
baseline and old prescriptions have been instantiated together.
-/

namespace SemigenericEPPA

universe u v w t z

variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {C : Type w} {L : Type t} [AddCommGroup L]
variable {V : Type z} {d : RawDatum G C}

/-- The residual matrix encoded from an actual raw colouring
of all ordered pairs; values within E-classes are dummy and never
used by the structural reversal or colour formulas. -/
def encodedInvariantResidual
    (encode : C → L) (colour : V → V → C) : V → V → L :=
  fun x y => encode (colour x y)

/-- Exact algebraic bridge from H-invariant raw colours to
an H-invariant affine residual matrix for the SAME base geometry.

The old-edge hypothesis is phrased with a fixed baseline b. It
ensures the encoded residual matrix agrees with b on each
cross-part old-old pair, exactly as required for zero outgoing
potential rows on the old subset. -/
theorem exists_encodedInvariantResidualMatrix
    (D : EffectiveGeometry d.s V)
    (rho : H →* Equiv.Perm V)
    (shift : G → L)
    (encode : C → L)
    (hEncodeReverse : ∀ c : C,
      encode (d.reverse c) = shift (d.phi c) - encode c)
    (colour : V → V → C)
    (hPhi : ∀ x y, ¬D.part x y →
      d.phi (colour x y) = D.F x y)
    (hReverse : ∀ x y, ¬D.part x y →
      colour y x = d.reverse (colour x y))
    (hInvariant : ∀ (h : H) (x y : V), ¬D.part x y →
      colour (rho h x) (rho h y) = colour x y)
    (S : Set V) (b : V → V → L)
    (hOld : ∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
      b x y = encode (colour x y)) :
    ∃ r : V → V → L,
      (∀ x y, ¬D.part x y →
        r y x = shift (D.F x y) - r x y) ∧
      (∀ (h : H) (x y : V), ¬D.part x y →
        r (rho h x) (rho h y) = r x y) ∧
      (∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
        r x y = b x y) := by
  let r := encodedInvariantResidual encode colour
  refine ⟨r, ?_, ?_, ?_⟩
  · intro x y hxy
    calc
      r y x = encode (colour y x) := rfl
      _ = encode (d.reverse (colour x y)) :=
        congrArg encode (hReverse x y hxy)
      _ = shift (d.phi (colour x y)) - encode (colour x y) :=
        hEncodeReverse (colour x y)
      _ = shift (D.F x y) - r x y := by
        rw [hPhi x y hxy]
        rfl
  · intro h x y hxy
    change encode (colour (rho h x) (rho h y)) =
      encode (colour x y)
    rw [hInvariant h x y hxy]
  · intro x y hx hy hxy
    exact (hOld x y hx hy hxy).symm

/-- Specialization to an ACTUAL affine residual code, without
supplying a separate global colour encoder or reversal proof.
This is the algebraic bridge from invariant raw orbit colouring to
the invariant matrix required by the fixed-cover H-action theorem. -/
theorem exists_codeInvariantResidualMatrix
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (rho : H →* Equiv.Perm V)
    (colour : V → V → C)
    (hPhi : ∀ x y, ¬D.part x y →
      d.phi (colour x y) = D.F x y)
    (hReverse : ∀ x y, ¬D.part x y →
      colour y x = d.reverse (colour x y))
    (hInvariant : ∀ (h : H) (x y : V), ¬D.part x y →
      colour (rho h x) (rho h y) = colour x y)
    (S : Set V) (b : V → V → L)
    (hOld : ∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
      b x y = code.encodeRaw (colour x y)) :
    ∃ r : V → V → L,
      (∀ x y, ¬D.part x y →
        r y x = code.shift (D.F x y) - r x y) ∧
      (∀ (h : H) (x y : V), ¬D.part x y →
        r (rho h x) (rho h y) = r x y) ∧
      (∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
        r x y = b x y) := by
  exact exists_encodedInvariantResidualMatrix
    D rho code.shift code.encodeRaw code.encodeRaw_reverse
    colour hPhi hReverse hInvariant S b hOld

end SemigenericEPPA
