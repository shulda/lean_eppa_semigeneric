import SemigenericEPPA.Bridge.TypedRawAutomorphismPermutation
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge

/-!
# The 3+1 involution-profile obstruction requires a good raw colour

The manuscript's negative coherent-EPPA argument when the
self-reversing effective-colour set S is EMPTY uses an involution
T on a raw rectangle structure with old vertices a,b,c in one
E-class and v in another. The involution interchanges a,b and
fixes c, while the effective profile from v to a,b,c is
respectively delta,1,1 with delta != 1.

Put w=T(v). If w belongs to the part of v, the rectangle on
rows v,w and columns a,c yields delta=1, contradiction.
Otherwise T exchanges the distinct-part pair v,w and
preserves its literal raw colour; therefore its raw colour is
self-reversing, so S is nonempty.

This lemma establishes the exact AUTOMORPHISM/GEOMETRY step
without assuming the old 3+1 presentation or a coherent
extension. In later steps the actual gadget and an upstream
coherent partial involution will construct these hypotheses.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {W : Type w} {d : RawDatum G C}

/-- A raw-colour-preserving involution of the full witness which
exchanges two old vertices a,b, fixes a third c in their E-class,
and sees the asymmetric old effective profile delta,1,1 from a
fourth vertex v, with delta ≠ 1, forces an ACTUAL self-reversing
raw colour to occur somewhere in the witness. -/
theorem RawRectanglePresentation.goodNonempty_of_threePointProfileInvolution
    (Q : RawRectanglePresentation d W)
    (T : Equiv.Perm W)
    (hTcolour : ∀ x y : W, Q.colour (T x) (T y) = Q.colour x y)
    (hT2 : ∀ x : W, T (T x) = x)
    (a b c v : W)
    (hab : Q.part a b)
    (hac : Q.part a c)
    (hva : ¬Q.part v a)
    (hTa : T a = b)
    (hTb : T b = a)
    (hTc : T c = c)
    (delta : G)
    (hdelta : delta ≠ 1)
    (hvaF : Q.effectiveReduct.F v a = delta)
    (hvbF : Q.effectiveReduct.F v b = 1)
    (hvcF : Q.effectiveReduct.F v c = 1) :
    d.selfReverseEffective.Nonempty := by
  classical
  let D : EffectiveGeometry d.s W := Q.effectiveReduct
  by_cases hvw : Q.part v (T v)
  · have hvwD : D.part v (T v) :=
      (Q.effectiveReduct_part v (T v)).mpr hvw
    have hacD : D.part a c :=
      (Q.effectiveReduct_part a c).mpr hac
    have hvaD : ¬D.part v a := by
      intro h
      exact hva ((Q.effectiveReduct_part v a).mp h)
    obtain ⟨hvcCross, hwacross, hwccross⟩ :=
      D.cross_square v (T v) a c hvwD hacD hvaD
    have hrawWa :
        Q.colour (T v) a = Q.colour v b := by
      calc
        Q.colour (T v) a = Q.colour (T v) (T b) := by rw [hTb]
        _ = Q.colour v b := hTcolour v b
    have hrawWc :
        Q.colour (T v) c = Q.colour v c := by
      calc
        Q.colour (T v) c = Q.colour (T v) (T c) := by rw [hTc]
        _ = Q.colour v c := hTcolour v c
    have hQa : ¬Q.part (T v) a := by
      intro h
      exact hwacross ((Q.effectiveReduct_part (T v) a).mpr h)
    have hQc : ¬Q.part (T v) c := by
      intro h
      exact hwccross ((Q.effectiveReduct_part (T v) c).mpr h)
    have hWa : D.F (T v) a = 1 :=
      (Q.effectiveReduct_equalColour (T v) a v b hrawWa hQa).trans hvbF
    have hWc : D.F (T v) c = 1 :=
      (Q.effectiveReduct_equalColour (T v) c v c hrawWc hQc).trans hvcF
    have hrect := D.rectangle v (T v) a c hvwD hacD hvaD
    have hinv : delta⁻¹ = 1 := by
      change (Q.effectiveReduct.F v a)⁻¹ *
          Q.effectiveReduct.F v c =
        (Q.effectiveReduct.F (T v) a)⁻¹ *
          Q.effectiveReduct.F (T v) c at hrect
      rw [hvaF, hvcF, hWa, hWc] at hrect
      simpa only [mul_one, one_inv, one_mul] using hrect
    have hcontra : delta = 1 := by
      have h := congrArg (fun x : G => x⁻¹) hinv
      simpa only [inv_inv, inv_one] using h
    exact False.elim (hdelta hcontra)
  · obtain ⟨raw, hraw⟩ :
        ∃ raw : C, Q.colour v (T v) = some raw := by
      cases hcol : Q.colour v (T v) with
      | none =>
          exact False.elim (hvw ((Q.colour_none_iff v (T v)).mp hcol))
      | some raw => exact ⟨raw, rfl⟩
    have hswap :
        Q.colour (T v) v = Q.colour v (T v) := by
      simpa only [hT2 v] using hTcolour v (T v)
    have hreverse : Q.colour (T v) v = some (d.reverse raw) := by
      rw [Q.colour_reverse v (T v), hraw]
      rfl
    have hfixed : d.reverse raw = raw :=
      Option.some.inj (hreverse.symm.trans (hswap.trans hraw))
    exact ⟨d.phi raw, raw, rfl, hfixed⟩

end SemigenericEPPA
