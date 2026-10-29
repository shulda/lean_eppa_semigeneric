import SemigenericEPPA.Structure.PartQuotient

/-!
# Bijective induced maps on actual E-part quotients

An E-reflecting map induces an injective map on the canonical quotient
of E-classes. If every target E-class intersects its image, this map
is bijective. Neither the original nor the target vertex set needs to
be nonempty, and finiteness is not required.

The statement is in the literal original binary E/R_c language.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {W : Type z}
variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) V}
variable {B : Structure (rectangleLanguage C) W}

/-- The induced map of genuine E-class quotients is bijective whenever
the underlying map preserves and reflects E and meets every target
class. The quotient is only over *nonempty* classes: no fake parts. -/
theorem partQuotientMap_bijective_of_partCover
    (hA : IsRectangleStructure d A)
    (hB : IsRectangleStructure d B)
    (f : V → W)
    (hpart : ∀ x y, partRel B (f x) (f y) ↔ partRel A x y)
    (hcover : ∀ w, ∃ x, partRel B (f x) w) :
    Function.Bijective
      (partQuotientMap hA hB f
        (fun x y hxy => (hpart x y).mpr hxy)) := by
  constructor
  · exact partQuotientMap_injective hA hB f
      (fun x y hxy => (hpart x y).mpr hxy)
      (fun x y hxy => (hpart x y).mp hxy)
  · intro q
    induction q using Quotient.inductionOn with
    | _ w =>
        obtain ⟨x, hx⟩ := hcover w
        refine ⟨partClass hA x, ?_⟩
        change Quotient.mk hB.partSetoid (f x) =
          Quotient.mk hB.partSetoid w
        exact Quotient.sound hx

/-- Package the canonical induced E-class map as an actual equivalence. -/
noncomputable def partQuotientEquivOfCover
    (hA : IsRectangleStructure d A)
    (hB : IsRectangleStructure d B)
    (f : V → W)
    (hpart : ∀ x y, partRel B (f x) (f y) ↔ partRel A x y)
    (hcover : ∀ w, ∃ x, partRel B (f x) w) :
    PartQuotient hA ≃ PartQuotient hB :=
  Equiv.ofBijective
    (partQuotientMap hA hB f
      (fun x y hxy => (hpart x y).mpr hxy))
    (partQuotientMap_bijective_of_partCover
      hA hB f hpart hcover)

end SemigenericEPPA
