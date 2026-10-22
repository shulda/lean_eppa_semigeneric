import SemigenericEPPA.Structure.FixedJointRawCover
import SemigenericEPPA.Structure.OldRawReferencePartialInvariance
import SemigenericEPPA.Bridge.BinaryRawAutomorphismSubgroup

/-!
# Individual raw groupoid connectors in the SAME fixed raw cover

The certified fixed joint raw cover J provides simultaneous individual
and homomorphic group lifts, but its individual API leaves the raw
old-reference equation as an input and returns a permutation with
external preservation proofs.

For any genuine original raw partial isomorphism, the reference
equation is a theorem: it follows from the literal old colours,
without any H-dependent change to J's baseline. If an automorphism
of J's prechosen effective base extends the selected partial arrow,
this file converts J.individual to a member of the EXACT SAME raw
automorphism subgroup used for the strict selected H-group actions.

Thus actual old connector extensions and stabilizer homomorphisms
will land in one common group, allowing the previously certified
groupoid normal form to combine them.

This does NOT assume that a suitable effective connector automorphism
exists; it is supplied separately by the fixed indexed-gauge partial
valuation construction.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t
variable {G : Type u} [Group G]
variable {C : Type v}
variable {U : Type w} {V : Type z}
variable {d : RawDatum G C}

/-- A genuine old E/raw-colour partial map, with an actual effective
automorphism extending its fixed old embedding, has an extension in
the LITERAL raw-automorphism subgroup of the SAME prechosen cover J.

The original raw reference is automatically invariant on all
selected cross-class pairs, not an independent assumption. -/
theorem FixedJointRawCover.exists_rawAutConnector_of_effectiveConnector
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (e : U → V)
    (J : FixedJointRawCover.{u, v, w, z, t} P D e)
    (he : Function.Injective e)
    (hPartEmbed : ∀ x y : U,
      D.part (e x) (e y) ↔ P.part x y)
    (S : Set U)
    (p : S → U)
    (hE : ∀ x y : S,
      P.part x.val y.val ↔ P.part (p x) (p y))
    (hRaw : ∀ x y : S,
      P.colour (p x) (p y) = P.colour x.val y.val)
    (theta : Equiv.Perm V)
    (hext : ∀ x : S, theta (e x.val) = e (p x))
    (hThetaE : ∀ x y : V,
      D.part (theta x) (theta y) ↔ D.part x y)
    (hThetaF : ∀ x y : V, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y) :
    ∃ beta : binaryRawAutSubgroup
        (fun X Y : RawCoverVertex V (UniversalResidualCarrier C) =>
          D.part X.1 Y.1)
        (fun c X Y =>
          rawRel (rawCoverPresentation D J.code J.baseline
            J.baseline_reverse).toStructure c X Y),
      ∀ x : S,
        beta.val
          (e x.val, fun _ : V => (0 : UniversalResidualCarrier C)) =
          (e (p x), fun _ : V => (0 : UniversalResidualCarrier C)) := by
  have hRef (x y : S) (hxy : ¬D.part (e x.val) (e y.val)) :
      oldRawReferenceOnBase P e J.defaultColour
          (e (p x)) (e (p y)) =
        oldRawReferenceOnBase P e J.defaultColour
          (e x.val) (e y.val) :=
    oldRawReferenceOnBase_partialInvariant P D e he J.defaultColour
      hPartEmbed S p hE hRaw x y hxy
  obtain ⟨perm, hOld, hPart, hRel⟩ :=
    J.individual S p theta hRef hext hThetaE hThetaF
  let E : RawCoverVertex V (UniversalResidualCarrier C) →
      RawCoverVertex V (UniversalResidualCarrier C) → Prop :=
    fun X Y => D.part X.1 Y.1
  let R : C → RawCoverVertex V (UniversalResidualCarrier C) →
      RawCoverVertex V (UniversalResidualCarrier C) → Prop :=
    fun c X Y =>
      rawRel (rawCoverPresentation D J.code J.baseline
        J.baseline_reverse).toStructure c X Y
  have hPres : PreservesBinaryRawRelations E R perm :=
    ⟨hPart, hRel⟩
  exact ⟨⟨perm, hPres⟩, hOld⟩

end SemigenericEPPA
