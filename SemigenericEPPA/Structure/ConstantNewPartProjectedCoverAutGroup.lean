import SemigenericEPPA.Structure.ConstantNewPartActualAutGroup

/-!
# Faithfully realizing arbitrary group extensions in original raw rectangles

Suppose a group Q already acts on a raw R1--R3 rectangle presentation P
by genuine E- and all-R_c-preserving automorphisms, and T is ANY
group with homomorphism π:T→Q.

Add one new E-class with carrier T, assigning one constant raw
cross-colour to every new-to-old edge. On old vertices T acts
through π; on the new class it acts by left translation. This is
an honest injective strict homomorphism from T into the group
preserving E and every original R_c. Its old restriction is EXACTLY
ρ(π(t)), regardless of whether ρ or π is injective.

This interface will be instantiated with T=the prescribed finite
F₂-chain relative cover, π its certified surjective projection, and
the split H≤Q copy. All necessary raw invariance is internal to
the previously certified one-new-class group action. No DLF
cofinality or safe-group extension conclusion is asserted.
-/

namespace SemigenericEPPA

universe u v w t z
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {Q : Type t} {T : Type z}
variable [Group Q] [Group T]
variable {d : RawDatum G C}

/-- The actual raw-automorphism-group realization of any
finite or infinite group homomorphism π:T→Q, on one new regular
E-class added to the original raw structure. -/
noncomputable def RawRectanglePresentation.adjoinCoverGroupAutHom
    (P : RawRectanglePresentation d V)
    (c0 : C)
    (rho : Q →* Equiv.Perm V)
    (π : T →* Q)
    (hPart : ∀ (q : Q) (x y : V),
      P.part (rho q x) (rho q y) ↔ P.part x y)
    (hColour : ∀ (q : Q) (x y : V),
      P.colour (rho q x) (rho q y) = P.colour x y) :
    T →* binaryRawAutSubgroup
      (fun x y : V ⊕ T =>
        (P.adjoinConstantNewPart (R := T) c0).part x y)
      (fun c x y =>
        (P.adjoinConstantNewPart (R := T) c0).colour x y = some c) :=
  P.adjoinRegularPartRawAutHom c0 (rho.comp π)
    (fun q x y => hPart (π q) x y)
    (fun q x y => hColour (π q) x y)

/-- The new regular E-class ensures faithfulness of T even if
π:T→Q has a nontrivial kernel and/or ρ is nonfaithful. -/
theorem RawRectanglePresentation.adjoinCoverGroupAutHom_injective
    (P : RawRectanglePresentation d V)
    (c0 : C)
    (rho : Q →* Equiv.Perm V)
    (π : T →* Q)
    (hPart : ∀ (q : Q) (x y : V),
      P.part (rho q x) (rho q y) ↔ P.part x y)
    (hColour : ∀ (q : Q) (x y : V),
      P.colour (rho q x) (rho q y) = P.colour x y) :
    Function.Injective
      (P.adjoinCoverGroupAutHom c0 rho π hPart hColour) :=
  P.adjoinRegularPartRawAutHom_injective c0 (rho.comp π)
    (fun q x y => hPart (π q) x y)
    (fun q x y => hColour (π q) x y)

/-- Every prescribed old point is moved by the projected old
action with no changes to the original raw embedding. -/
theorem RawRectanglePresentation.adjoinCoverGroupAutHom_old
    (P : RawRectanglePresentation d V)
    (c0 : C)
    (rho : Q →* Equiv.Perm V)
    (π : T →* Q)
    (hPart : ∀ (q : Q) (x y : V),
      P.part (rho q x) (rho q y) ↔ P.part x y)
    (hColour : ∀ (q : Q) (x y : V),
      P.colour (rho q x) (rho q y) = P.colour x y)
    (a : T) (x : V) :
    (P.adjoinCoverGroupAutHom c0 rho π hPart hColour a).val
        (.inl x) = .inl (rho (π a) x) := rfl

end SemigenericEPPA
