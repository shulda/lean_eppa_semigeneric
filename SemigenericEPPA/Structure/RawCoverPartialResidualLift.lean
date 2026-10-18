import SemigenericEPPA.Structure.RawCoverPrescribedLift

/-!
# Lifting partial maps of distinguished raw-cover vertices

Let an effective automorphism theta extend an injective partial
map p:S→V, and let eta(x,-) be one chosen complete raw residual
valuation over each old base vertex x.

Assume p preserves the *canonical residual labels* of all old
cross-part edges, not merely their decoded raw colour:
  ell_eta(p x,p y)=ell_eta(x,y).

The full prescribed raw-lift theorem can be applied without an
extra target valuation family. Set etaTarget(x,-)=eta(p x,-)
on the partial domain, and use arbitrary values off that domain.
The resulting automorphism of the SAME raw cover sends each
distinguished old vertex (x,eta x) precisely to
(p x,eta(p x)), preserving all original raw predicates.

This is the relative raw EPPA transport in base-carrier notation.
The remaining raw EPPA assembly must transport the actual old
partial map along the effective embedding and derive the canonical
residual-label equality from raw colour preservation and sections.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z
variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L] {V : Type z}
variable {d : RawDatum G C}

/-- Every old partial map preserving exact canonical residual labels
extends on the raw cover whenever its effective base map extends.
The whole old vertex, not just its base or its raw colour, is mapped
to the chosen old image. -/
theorem exists_rawCoverLift_of_partialResidualMap
    [Finite V]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (eta : V → V → L)
    (S : Set V) (p : S → V)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y)
    (hp : ∀ x : S, theta x.val = p x)
    (hlabel : ∀ x y : S, ¬D.part x.val y.val →
      rawResidual (eta (p x) (p y)) (eta (p y) (p x))
          (b (p x) (p y)) =
        rawResidual (eta x.val y.val) (eta y.val x.val)
          (b x.val y.val)) :
    ∃ T : RawCoverVertex V L ≃ RawCoverVertex V L,
      (∀ x : S, T (x.val, eta x.val) = (p x, eta (p x))) ∧
      (∀ X Y : RawCoverVertex V L,
        D.part (T X).1 (T Y).1 ↔ D.part X.1 Y.1) ∧
      (∀ c : C, ∀ X Y : RawCoverVertex V L,
        rawRel (rawCoverPresentation D code b hb).toStructure c (T X) (T Y) ↔
        rawRel (rawCoverPresentation D code b hb).toStructure c X Y) := by
  classical
  let etaTarget : V → V → L :=
    fun z => if hz : z ∈ S then eta (p ⟨z, hz⟩) else eta z
  have htarget (x : S) : etaTarget x.val = eta (p x) := by
    simp [etaTarget, x.property]
  have hlabels :
      ∀ x y : V, x ∈ S → y ∈ S → ¬D.part x y →
        rawResidual (etaTarget x (theta y))
            (etaTarget y (theta x)) (b (theta x) (theta y)) =
          rawResidual (eta x y) (eta y x) (b x y) := by
    intro x y hx hy hxy
    let xx : S := ⟨x, hx⟩
    let yy : S := ⟨y, hy⟩
    have hx' := htarget xx
    have hy' := htarget yy
    change etaTarget x = eta (p xx) at hx'
    change etaTarget y = eta (p yy) at hy'
    rw [hx', hy', hp xx, hp yy]
    exact hlabel xx yy hxy
  obtain ⟨T, hpoints, hparts, hcolours⟩ :=
    exists_rawCoverAutomorphism_extending_old
      D code b hb theta hE hF S eta etaTarget hlabels
  refine ⟨T, ?_, hparts, hcolours⟩
  intro x
  calc
    T (x.val, eta x.val) =
        (theta x.val, etaTarget x.val) := hpoints x.val x.property
    _ = (p x, eta (p x)) := by
      rw [hp x, htarget x]

end SemigenericEPPA
