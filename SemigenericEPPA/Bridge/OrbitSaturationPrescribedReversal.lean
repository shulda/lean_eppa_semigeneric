import SemigenericEPPA.Bridge.OrbitSaturationPrescribedColours

/-!
# Reversal consistency on the H-saturation of noninvariant old colours

The distinguished B phase-one copy in relative EPPA is stable
under reversal of ordered cross-pairs, but not under the H-action.
The return-consistency lemma constructs a global H-invariant
colour extension. It remains to show the extension still
respects RAW reversal on the entire H-saturation of B's pairs.

If tau is an involution commuting with H, then the H-saturation
of a tau-invariant subset is tau-invariant. On such saturated
orbits the extended colours reverse correctly because every
saturated point has a representative in the original S,
H-invariance transports it back to that representative, and
the original raw colour reversal is unchanged.

Crucially, we impose NO reversal condition on the complement
of the saturation yet. On that complement the invariant raw
orbit selection theorem will select new raw colours, using
actual reversal-safe fibre conditions only for reversed H-orbits.

No global H-invariance of the original S is assumed.
-/

namespace SemigenericEPPA

universe u v w
variable {H : Type u} [Group H]
variable {A : Type v} {C : Type w}

/-- Saturation of a reversal-stable but possibly non-H-invariant
subset remains reversal-stable, provided reversal commutes with H. -/
theorem orbitSaturation_reverse_iff
    (rho : H →* Equiv.Perm A)
    (tau : A → A)
    (htau : Function.Involutive tau)
    (hCommute : ∀ (h : H) (a : A),
      tau (rho h a) = rho h (tau a))
    (S : Set A)
    (hSrev : ∀ a : A, a ∈ S ↔ tau a ∈ S) :
    ∀ a : A, a ∈ orbitSaturation rho S ↔
      tau a ∈ orbitSaturation rho S := by
  have forward (a : A)
      (ha : a ∈ orbitSaturation rho S) :
      tau a ∈ orbitSaturation rho S := by
    obtain ⟨b, hb, h, hba⟩ := ha
    refine ⟨tau b, (hSrev b).mp hb, h, ?_⟩
    calc
      rho h (tau b) = tau (rho h b) := (hCommute h b).symm
      _ = tau a := congrArg tau hba
  intro a
  constructor
  · exact forward a
  · intro hta
    have hh := forward (tau a) hta
    simpa only [htau a] using hh

/-- Every H-invariant extension which agrees with old on S
automatically reverses correctly on the ENTIRE H-saturation,
not only on the old S itself. -/
theorem invariantExtension_reverses_on_orbitSaturation
    (rho : H →* Equiv.Perm A)
    (tau : A → A)
    (hCommute : ∀ (h : H) (a : A),
      tau (rho h a) = rho h (tau a))
    (reverse : C → C)
    (S : Set A)
    (hSrev : ∀ a : A, a ∈ S ↔ tau a ∈ S)
    (old : A → C)
    (hOldReverse : ∀ a : A, a ∈ S →
      old (tau a) = reverse (old a))
    (colour : A → C)
    (hExtend : ∀ a : A, a ∈ S → colour a = old a)
    (hInvariant : ∀ (h : H) (a : A),
      colour (rho h a) = colour a) :
    ∀ a : A, a ∈ orbitSaturation rho S →
      colour (tau a) = reverse (colour a) := by
  intro a ha
  obtain ⟨b, hb, h, hba⟩ := ha
  calc
    colour (tau a) = colour (tau (rho h b)) := by rw [hba]
    _ = colour (rho h (tau b)) := by rw [hCommute h b]
    _ = colour (tau b) := hInvariant h (tau b)
    _ = old (tau b) := hExtend (tau b) ((hSrev b).mp hb)
    _ = reverse (old b) := hOldReverse b hb
    _ = reverse (colour b) := by rw [hExtend b hb]
    _ = reverse (colour a) := by
      rw [← hba, hInvariant h b]

/-- Exactly the data needed before choosing new raw colours on
unspecified H-orbits: an old-colour extension which preserves
both H-action globally and reversal on all occupied/saturated
old pairs, despite noninvariance of the initially prescribed S. -/
theorem exists_invariantReversingColour_on_orbitSaturation
    [Nonempty C]
    (rho : H →* Equiv.Perm A)
    (tau : A → A)
    (hCommute : ∀ (h : H) (a : A),
      tau (rho h a) = rho h (tau a))
    (reverse : C → C)
    (S : Set A)
    (hSrev : ∀ a : A, a ∈ S ↔ tau a ∈ S)
    (old : A → C)
    (hOldReverse : ∀ a : A, a ∈ S →
      old (tau a) = reverse (old a))
    (hReturn : ∀ (h : H) (a : A),
      a ∈ S → rho h a ∈ S →
      old (rho h a) = old a) :
    ∃ colour : A → C,
      (∀ a : A, a ∈ S → colour a = old a) ∧
      (∀ (h : H) (a : A),
        colour (rho h a) = colour a) ∧
      (∀ a : A, a ∈ orbitSaturation rho S →
        colour (tau a) = reverse (colour a)) := by
  obtain ⟨colour, hExtend, hInvariant⟩ :=
    exists_invariantColour_extending_nonInvariantSubset rho S old hReturn
  exact ⟨colour, hExtend, hInvariant,
    invariantExtension_reverses_on_orbitSaturation
      rho tau hCommute reverse S hSrev old hOldReverse
      colour hExtend hInvariant⟩

end SemigenericEPPA
