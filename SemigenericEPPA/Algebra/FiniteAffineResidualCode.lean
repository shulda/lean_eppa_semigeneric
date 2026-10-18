import SemigenericEPPA.Algebra.EquivariantFibreRetraction
import SemigenericEPPA.Algebra.UniversalResidualEncoderInjective
import SemigenericEPPA.Algebra.AffineResidualCode
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Abel

/-!
# Unconditional finite affine residual code (3.20)

For every finite raw datum d=(G,C,s,*,phi), construct an actual
AffineResidualCode on the explicit finite coefficient group

                 L = (C -> ZMod 4) × ZMod 2.

The encoder was already proved injective and to intertwine
raw reversal with the affine involution l ↦ t(g)-l.

Instead of manually gluing decoders on the one- and two-element
orbits of effective reversal, consider the *entire indexed bundle*
A=G×L, with involution (g,l) ↦ (s(g),t(g)-l).
The encoder is an equivariant injection C -> A over the effective
index G. Our fibre-preserving equivariant retraction theorem
constructs q:A->C simultaneously on ALL fibres.

The only fixed-point obstruction occurs when s(g)=g and
t(g)-l=l. By the universal shift construction this forces the
existence of a reversal-fixed raw colour over g, precisely what
the retraction needs.

The resulting decoder and section satisfy BOTH strict typed
equations of (3.20), and the group L is finite even when C is
empty (subject to the raw datum's surjectivity, as usual).
No external choice of raw fibre codes or noncommutativity
assumption is made.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

/-- The manuscript's finite affine residual code exists for every
finite raw alphabet and finite effective group, with one explicit
common residual coefficient group. The statement delivers the
actual fully populated code, not a partial encoder interface. -/
theorem exists_universalAffineResidualCode
    [Finite G] [Finite C]
    (d : RawDatum G C) :
    Nonempty (AffineResidualCode d (UniversalResidualCarrier C)) := by
  classical
  let L := UniversalResidualCarrier C
  letI : Finite L := finite_universalResidualCarrier
  letI : Fintype G := Fintype.ofFinite _
  letI : Fintype L := Fintype.ofFinite _
  let A := G × L
  letI : Fintype A := inferInstance
  letI : LinearOrder A :=
    LinearOrder.lift' (Fintype.equivFin A)
      (Fintype.equivFin A).injective
  let shift : G → L := universalResidualShift d
  let enc : C → L := universalResidualEncode d
  let rA : A → A := fun a => (d.s a.1, shift a.1 - a.2)
  let e : C → A := fun c => (d.phi c, enc c)
  have hrA : Function.Involutive rA := by
    rintro ⟨g, l⟩
    apply Prod.ext
    · exact d.s.involutive g
    · change shift (d.s g) - (shift g - l) = l
      rw [universalResidualShift_reverse d g]
      abel
  have he : Function.Injective e := by
    intro c c' h
    apply universalResidualEncode_injective d
    exact congrArg Prod.snd h
  have hequiv : ∀ c : C, e (d.reverse c) = rA (e c) := by
    intro c
    apply Prod.ext
    · exact d.equivariant c
    · change enc (d.reverse c) = shift (d.phi c) - enc c
      exact universalResidualEncode_reverse d c
  have hindexA : ∀ a : A, a.1 = a.1 := fun _ => rfl
  have hrevIndexA : ∀ a : A, (rA a).1 = d.s a.1 := by
    intro a
    rfl
  have hfixed : ∀ a : A, rA a = a →
      ∃ c : C, d.phi c = a.1 ∧ d.reverse c = c := by
    rintro ⟨g, l⟩ h
    have hg : d.s g = g := congrArg Prod.fst h
    have hl : shift g - l = l := congrArg Prod.snd h
    by_cases hs : g ∈ d.selfReverseEffective
    · obtain ⟨c, hc, hrev⟩ := hs
      exact ⟨c, hc, hrev⟩
    · exact False.elim
        ((universalResidualShift_free d g hg hs l) hl)
  obtain ⟨q, hqe, hqphi, hqrev⟩ :=
    exists_equivariantFibreRetraction
      rA hrA d.reverse d.reverse_involutive d.s
      (fun a : A => a.1) d.phi
      hrevIndexA d.equivariant e he hequiv
      (fun _ => rfl) d.phi_surjective hfixed
  let decoder : ∀ g : G, L → d.fibre g :=
    fun g l => ⟨q (g, l), hqphi (g, l)⟩
  let encoder : ∀ g : G, d.fibre g → L :=
    fun _ c => enc c.val
  have hsection : ∀ (g : G) (c : d.fibre g),
      decoder g (encoder g c) = c := by
    intro g c
    apply Subtype.ext
    change q (g, enc c.val) = c.val
    have hc := hqe c.val
    change q (d.phi c.val, enc c.val) = c.val at hc
    simpa only [c.property] using hc
  have hdecReverse : ∀ (g : G) (l : L),
      decoder (d.s g) (shift g - l) =
        d.reverseFibre g (decoder g l) := by
    intro g l
    apply Subtype.ext
    change q (d.s g, shift g - l) = d.reverse (q (g, l))
    exact hqrev (g, l)
  have hencReverse : ∀ (g : G) (c : d.fibre g),
      encoder (d.s g) (d.reverseFibre g c) =
        shift g - encoder g c := by
    intro g c
    change enc (d.reverse c.val) = shift g - enc c.val
    have hc := universalResidualEncode_reverse d c.val
    change enc (d.reverse c.val) =
      shift (d.phi c.val) - enc c.val at hc
    simpa only [c.property] using hc
  exact ⟨{
    shift := shift
    shift_reverse := universalResidualShift_reverse d
    decode := decoder
    encode := encoder
    decode_encode := hsection
    decode_reverse := hdecReverse
    encode_reverse := hencReverse
  }⟩

end SemigenericEPPA
