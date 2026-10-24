import SemigenericEPPA.Structure.RawPresentation

/-!
# Transport full partial-raw-map connector extensions to an induced substructure

Suppose an original raw P embeds as an induced substructure of a
larger finite or infinite original raw R via e. Suppose there is
also an embedding f of R into an action carrier Y, and a family
of actions on Y which realizes EVERY partial raw automorphism
of R on the image of f.

Then the SAME acting family also realizes every partial raw
automorphism of P on the image of f ∘ e. The proof uses an
equivalence between the old selected partial domain and its image
under the injective induced embedding; it never assumes an action
on all new points of R by the old group.

This is a general original-language transport lemma independent of
good colours, JEP, strong amalgamation, finite carriers or group laws.
-/

namespace SemigenericEPPA

universe u v w t z q
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {X : Type t} {Y : Type z}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Any family of connectors realizing all partial raw
automorphisms of a larger presentation also realizes every
partial raw automorphism of any induced subpresentation, in the
same acting target and with the same original vertex embedding. -/
theorem partialConnectors_restrict_to_induced
    (P : RawRectanglePresentation d V)
    (R : RawRectanglePresentation d X)
    (e : V → X)
    (eInj : Function.Injective e)
    (ePart : ∀ x y : V, R.part (e x) (e y) ↔ P.part x y)
    (eColour : ∀ x y : V,
      R.colour (e x) (e y) = P.colour x y)
    (f : X → Y)
    {K : Type q} (act : K → Y → Y)
    (hFull : ∀ (T : Set X) (r : T → X),
      Function.Injective r →
      (∀ x y : T, R.part x.val y.val ↔
        R.part (r x) (r y)) →
      (∀ x y : T, R.colour (r x) (r y) =
        R.colour x.val y.val) →
      ∃ k : K, ∀ x : T, act k (f x.val) = f (r x)) :
    ∀ (S : Set V) (p : S → V),
      Function.Injective p →
      (∀ x y : S, P.part x.val y.val ↔
        P.part (p x) (p y)) →
      (∀ x y : S, P.colour (p x) (p y) =
        P.colour x.val y.val) →
      ∃ k : K, ∀ x : S, act k (f (e x.val)) = f (e (p x)) := by
  classical
  intro S p hp hPart hColour
  let S' : Set X := Set.range (fun x : S => e x.val)
  let core : S → S' :=
    fun x => ⟨e x.val, ⟨x, rfl⟩⟩
  have hCoreInj : Function.Injective core := by
    intro x y h
    apply Subtype.ext
    apply eInj
    exact congrArg Subtype.val h
  have hCoreSurj : Function.Surjective core := by
    intro z
    obtain ⟨x, hx⟩ := z.property
    exact ⟨x, Subtype.ext hx⟩
  let eqv : S ≃ S' :=
    Equiv.ofBijective core ⟨hCoreInj, hCoreSurj⟩
  have hEqvVal (x : S) : (eqv x).val = e x.val := rfl
  have hSymmVal (x : S') : x.val = e (eqv.symm x).val := by
    have h := congrArg Subtype.val (eqv.apply_symm_apply x)
    exact h.symm
  let r : S' → X := fun x => e (p (eqv.symm x))
  have hrInj : Function.Injective r := by
    intro x y hxy
    apply eqv.symm.injective
    apply hp
    exact eInj hxy
  have hrPart : ∀ x y : S',
      R.part x.val y.val ↔ R.part (r x) (r y) := by
    intro x y
    let a : S := eqv.symm x
    let b : S := eqv.symm y
    change R.part x.val y.val ↔ R.part (e (p a)) (e (p b))
    calc
      R.part x.val y.val ↔ R.part (e a.val) (e b.val) := by
        rw [hSymmVal x, hSymmVal y]
      _ ↔ P.part a.val b.val := ePart a.val b.val
      _ ↔ P.part (p a) (p b) := hPart a b
      _ ↔ R.part (e (p a)) (e (p b)) :=
        (ePart (p a) (p b)).symm
  have hrColour : ∀ x y : S',
      R.colour (r x) (r y) = R.colour x.val y.val := by
    intro x y
    let a : S := eqv.symm x
    let b : S := eqv.symm y
    change R.colour (e (p a)) (e (p b)) = R.colour x.val y.val
    calc
      R.colour (e (p a)) (e (p b)) = P.colour (p a) (p b) :=
        eColour (p a) (p b)
      _ = P.colour a.val b.val := hColour a b
      _ = R.colour (e a.val) (e b.val) :=
        (eColour a.val b.val).symm
      _ = R.colour x.val y.val := by
        rw [hSymmVal x, hSymmVal y]
  obtain ⟨k, hk⟩ := hFull S' r hrInj hrPart hrColour
  refine ⟨k, ?_⟩
  intro x
  have hx := hk (eqv x)
  change act k (f (e x.val)) = f (e (p (eqv.symm (eqv x)))) at hx
  simpa only [eqv.symm_apply_apply] using hx

end RawRectanglePresentation
end SemigenericEPPA
