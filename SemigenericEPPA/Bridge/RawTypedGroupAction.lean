import SemigenericEPPA.Bridge.RawTypedAutomorphism

/-!
# Converting homomorphic raw permutation actions to typed automorphisms

A fixed-cover group lift supplies a homomorphism
rho : H →* Perm(V) that preserves E and each binary raw predicate P_c.
For coherent EPPA we will use the upstream AllThoseEPPA.Structure
automorphism API, including its composition convention.

Here we convert any such action into a family of actual typed total
automorphisms and verify the identity and multiplication laws.
No second language is introduced, and the language component is
literally the identity element of the trivial symbol-action group.

The upstream Structure.Automorphism exposes identity and composition
but not a separate group instance, so the group action laws are
formulated directly with id and comp.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w} {V : Type t}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

variable (P : RawRectanglePresentation d V)

/-- An H-action preserving the literal E predicate and each P_c
preserves the entire Option-valued ordered raw colour, including
the uncoloured E-related case. -/
theorem rawGroupAction_colour
    (rho : H →* Equiv.Perm V)
    (hPart : ∀ h : H, ∀ x y : V,
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hRaw : ∀ h : H, ∀ c : C, ∀ x y : V,
      rawRel P.toStructure c (rho h x) (rho h y) ↔
        rawRel P.toStructure c x y)
    (h : H) (x y : V) :
    P.colour (rho h x) (rho h y) = P.colour x y := by
  cases hc : P.colour x y with
  | none =>
    have hOld : P.part x y := (P.colour_none_iff x y).mp hc
    have hNew : P.part (rho h x) (rho h y) :=
      (hPart h x y).mpr hOld
    exact ((P.colour_none_iff _ _).mpr hNew).trans hc.symm
  | some c =>
    have hOld : rawRel P.toStructure c x y := hc
    have hNew := (hRaw h c x y).mpr hOld
    change P.colour (rho h x) (rho h y) = some c at hNew
    exact hNew.trans hc.symm

/-- The exact typed automorphism associated with one H-element,
retaining the concrete underlying vertex permutation. -/
def rawGroupAction_typed
    (rho : H →* Equiv.Perm V)
    (hPart : ∀ h : H, ∀ x y : V,
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hRaw : ∀ h : H, ∀ c : C, ∀ x y : V,
      rawRel P.toStructure c (rho h x) (rho h y) ↔
        rawRel P.toStructure c x y)
    (h : H) :
    Structure.Automorphism
      (Language.Action.trivial (rectangleLanguage C)
        (Equiv.Perm (Fin 0))) P.toStructure :=
  P.toTypedAutomorphism (rho h) (hPart h)
    (P.rawGroupAction_colour rho hPart hRaw h)

@[simp] theorem rawGroupAction_typed_apply
    (rho : H →* Equiv.Perm V)
    (hPart : ∀ h : H, ∀ x y : V,
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hRaw : ∀ h : H, ∀ c : C, ∀ x y : V,
      rawRel P.toStructure c (rho h x) (rho h y) ↔
        rawRel P.toStructure c x y)
    (h : H) (x : V) :
    P.rawGroupAction_typed rho hPart hRaw h x = rho h x :=
  rfl

/-- The typed action of the identity is exactly the upstream
identity automorphism, not merely pointwise equivalent to it. -/
theorem rawGroupAction_typed_one
    (rho : H →* Equiv.Perm V)
    (hPart : ∀ h : H, ∀ x y : V,
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hRaw : ∀ h : H, ∀ c : C, ∀ x y : V,
      rawRel P.toStructure c (rho h x) (rho h y) ↔
        rawRel P.toStructure c x y) :
    P.rawGroupAction_typed rho hPart hRaw 1 =
      Structure.Automorphism.id P.toStructure := by
  apply Structure.Automorphism.ext_of_lang_apply
  · rfl
  · intro x
    change rho 1 x = x
    simp

/-- The typed lifts respect group multiplication with the correct
order of composition used by the upstream coherent groupoid API. -/
theorem rawGroupAction_typed_mul
    (rho : H →* Equiv.Perm V)
    (hPart : ∀ h : H, ∀ x y : V,
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hRaw : ∀ h : H, ∀ c : C, ∀ x y : V,
      rawRel P.toStructure c (rho h x) (rho h y) ↔
        rawRel P.toStructure c x y)
    (h k : H) :
    P.rawGroupAction_typed rho hPart hRaw (h * k) =
      (P.rawGroupAction_typed rho hPart hRaw h).comp
        (P.rawGroupAction_typed rho hPart hRaw k) := by
  apply Structure.Automorphism.ext_of_lang_apply
  · rfl
  · intro x
    change rho (h * k) x = rho h (rho k x)
    rw [map_mul]
    rfl

end RawRectanglePresentation

end SemigenericEPPA
