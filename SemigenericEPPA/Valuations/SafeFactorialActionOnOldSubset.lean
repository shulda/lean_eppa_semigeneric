import SemigenericEPPA.Valuations.FactorialSafeReplicatedAction
import SemigenericEPPA.Valuations.OccupiedQuotientActionFixed
import SemigenericEPPA.Structure.InducedEffectiveGeometry
import SemigenericEPPA.Structure.TotalOldRawPalette
import SemigenericEPPA.Structure.SubsingletonFixedPartGeometry

/-!
# Safe H-actions on a fixed factorial carrier, from actual old structure data

Fix an ORIGINAL finite raw rectangle presentation P in the trivial
effective group sector G=1, and fix an injection
  j : A ↪ Fin(|A|!)
once and for all, BEFORE any H-action or induced subset S⊆A.

For an arbitrary group H acting by actual E- and raw-colour-preserving
automorphisms of S, construct:
* the action on old quotient E-class indices, fixing all unused indices;
* the canonical class multiplicities from the predetermined factorial;
* the classwise old injections induced by j;
* a genuine homomorphism H→Perm((A/E)×Fin(|A|!)) preserving E/F,
  extending the old vertices EXACTLY, and with every swapped
  cross-E pair admitting an honest self-reversing raw colour.

No chosen quotient-index action, cardinality divisibility, classwise
replica identifications, H-dependent ambient carrier, or abstract
old raw-colour reference remains as a theorem input. This is the
positive coherent G=1 SAFE EFFECTIVE action for every induced old
substructure, not yet a raw-cover H-lift or coherent groupoid functor.
-/

namespace SemigenericEPPA

universe u v w t

variable {G : Type u} [Group G] [Subsingleton G]
variable {C : Type v} {A : Type w} [Fintype A]
variable {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Every actual H-action on ANY induced old subset preserving E and
all ordered raw colours has a strictly safe action on the SAME old
factorial-padded effective carrier, with fixed old embedding. -/
theorem exists_safeFactorialAction_onOldSubset
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (S : Set A)
    (rho : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      P.part x.val y.val ↔
        P.part (rho h x).val (rho h y).val)
    (hRaw : ∀ (h : H) (x y : S),
      P.colour (rho h x).val (rho h y).val =
        P.colour x.val y.val) :
    ∃ theta : H →* Equiv.Perm
        (Quotient P.effectiveReduct.part ×
          Fin (coherentPaddingSize A)),
      (∀ (h : H) (x : S),
        theta h (Quotient.mk P.effectiveReduct.part x.val,
            j x.val) =
          (Quotient.mk P.effectiveReduct.part (rho h x).val,
            j (rho h x).val)) ∧
      (∀ (h : H) (x y : Quotient P.effectiveReduct.part ×
          Fin (coherentPaddingSize A)),
        (subsingletonFixedPartGeometry d.s
          (Quotient P.effectiveReduct.part)
          (coherentPaddingSize A)).part (theta h x) (theta h y) ↔
        (subsingletonFixedPartGeometry d.s
          (Quotient P.effectiveReduct.part)
          (coherentPaddingSize A)).part x y) ∧
      (∀ (h : H) (x y : Quotient P.effectiveReduct.part ×
          Fin (coherentPaddingSize A)),
        ¬(subsingletonFixedPartGeometry d.s
          (Quotient P.effectiveReduct.part)
          (coherentPaddingSize A)).part x y →
        (subsingletonFixedPartGeometry d.s
          (Quotient P.effectiveReduct.part)
          (coherentPaddingSize A)).F (theta h x) (theta h y) =
        (subsingletonFixedPartGeometry d.s
          (Quotient P.effectiveReduct.part)
          (coherentPaddingSize A)).F x y) ∧
      (∀ (h : H) (x y : Quotient P.effectiveReduct.part ×
          Fin (coherentPaddingSize A)),
        ¬(subsingletonFixedPartGeometry d.s
          (Quotient P.effectiveReduct.part)
          (coherentPaddingSize A)).part x y →
        theta h x = y → theta h y = x →
        ∃ c : C, d.phi c =
            (subsingletonFixedPartGeometry d.s
              (Quotient P.effectiveReduct.part)
              (coherentPaddingSize A)).F x y ∧
          d.reverse c = c) := by
  classical
  let D := P.effectiveReduct
  let I := Quotient D.part
  let cls : S → I := fun x => Quotient.mk D.part x.val
  let B := subsingletonFixedPartGeometry d.s I (coherentPaddingSize A)
  let DS := D.induced S
  letI : Fintype S := Fintype.ofFinite S
  have hE' : ∀ (h : H) (x y : S),
      D.part x.val y.val ↔
        D.part (rho h x).val (rho h y).val := by
    intro h x y
    simpa only [P.effectiveReduct_part] using hE h x y
  obtain ⟨iota, hiota, hfix⟩ :=
    D.exists_occupiedQuotientGroupAction_fixed S rho hE'
  have hcls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x) :=
    fun h x => (hiota h x).symm
  have hDpart (x y : S) : DS.part x y ↔ cls x = cls y := by
    change D.part x.val y.val ↔
      Quotient.mk D.part x.val = Quotient.mk D.part y.val
    exact ⟨Quotient.sound, Quotient.exact⟩
  have hBpart (x y : I × Fin (coherentPaddingSize A)) :
      B.part x y ↔ x.1 = y.1 :=
    subsingletonFixedPartGeometry_part d.s I (coherentPaddingSize A) x y
  let old : S → S → C :=
    fun x y => P.totalOldRawColour x.val y.val
  have hPhi (x y : S) (hxy : ¬DS.part x y) :
      d.phi (old x y) = DS.F x y := by
    have hcross : ¬P.part x.val y.val := hxy
    exact P.totalOldRawColour_phi x.val y.val hcross
  have hReverse (x y : S) (hxy : ¬DS.part x y) :
      old y x = d.reverse (old x y) := by
    have hcross : ¬P.part x.val y.val := hxy
    exact P.totalOldRawColour_reverse x.val y.val hcross
  have hRaw' (h : H) (x y : S) (hxy : ¬DS.part x y) :
      old (rho h x) (rho h y) = old x y := by
    have hcross : ¬P.part x.val y.val := hxy
    have hcross' : ¬P.part (rho h x).val (rho h y).val := by
      intro hpart
      exact hcross ((hE h x y).mpr hpart)
    have hnew := P.totalOldRawColour_cross
      (rho h x).val (rho h y).val hcross'
    have hold := P.totalOldRawColour_cross x.val y.val hcross
    apply Option.some.inj
    calc
      some (old (rho h x) (rho h y)) =
          P.colour (rho h x).val (rho h y).val := hnew.symm
      _ = P.colour x.val y.val := hRaw h x y
      _ = some (old x y) := hold
  let jclass (i : ReplicatedOccupiedIndex cls)
      (x : ReplicatedOldFibre cls i) :
      Fin (coherentPaddingSize A) := j x.val.val
  have hjclass (i : ReplicatedOccupiedIndex cls) :
      Function.Injective (jclass i) := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hj hxy
  obtain ⟨theta, hOld, _hIndex, hPart, hColour, hSafe⟩ :=
    exists_factorialSafeReplicatedFixedCarrierAction
      (A := A) d DS B (Subtype.val : S → A)
      Subtype.val_injective cls hDpart hBpart old
      hPhi hReverse rho iota hcls hfix hRaw'
      jclass hjclass
  refine ⟨theta, ?_, hPart, hColour, hSafe⟩
  intro h x
  simpa only [fixedReplicaOldMap, cls, jclass]
    using hOld h x

end RawRectanglePresentation

end SemigenericEPPA
