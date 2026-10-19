import SemigenericEPPA.Structure.OldRawReferencePartialInvariance

/-!
# Genuine old raw group actions preserve the fixed extended reference

Given a group H acting by raw automorphisms on an induced old subset
S⊆U, and any homomorphic action on an effective base V extending
its action along a fixed old embedding e:U↪V, the global reference
oldRawReferenceOnBase is literally H-invariant on the embedded S.

This is proved by applying the individual old-partial-map reference
invariance lemma to each group element, rather than making a new
reference or raw baseline for H. It discharges a key hypothesis of
the fixed raw-cover group-lift construction.
-/

namespace SemigenericEPPA

universe u v w z t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w}
variable {U : Type z} {V : Type t}
variable {d : RawDatum G C}

/-- Any H-action on the ambient effective base which extends actual
old raw automorphisms preserves the reference on the embedded
H-stable subset of old vertices, for every cross-E ordered pair. -/
theorem oldRawReferenceOnBase_groupInvariant
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (e : U → V) (he : Function.Injective e)
    (c₀ : C)
    (hPart : ∀ x y : U,
      D.part (e x) (e y) ↔ P.part x y)
    (S : Set U)
    (rho : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      P.part x.val y.val ↔ P.part (rho h x).val (rho h y).val)
    (hRaw : ∀ (h : H) (x y : S),
      P.colour (rho h x).val (rho h y).val =
        P.colour x.val y.val)
    (rhoB : H →* Equiv.Perm V)
    (hExt : ∀ (h : H) (x : S),
      rhoB h (e x.val) = e (rho h x).val)
    (h : H) (x y : V)
    (hx : x ∈ Set.range (fun a : S => e a.val))
    (hy : y ∈ Set.range (fun a : S => e a.val))
    (hcross : ¬D.part x y) :
    oldRawReferenceOnBase P e c₀ (rhoB h x) (rhoB h y) =
      oldRawReferenceOnBase P e c₀ x y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [hExt h a, hExt h b]
  exact oldRawReferenceOnBase_partialInvariant
    P D e he c₀ hPart S (fun x : S => (rho h x).val)
      (hE h) (hRaw h) a b hcross

end SemigenericEPPA
