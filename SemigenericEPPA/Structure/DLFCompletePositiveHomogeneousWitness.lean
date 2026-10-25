import SemigenericEPPA.Structure.DLFUniversalAgeTowerFin
import SemigenericEPPA.Structure.DLFNormalizeFiniteRawToFin
import SemigenericEPPA.Structure.DLFSafePairTowerCountableLimit
import SemigenericEPPA.Structure.DLFTrivialSafePairSeed

/-!
# A countable homogeneous original-language DLF limit from ONE complete good orbit

The positive DLF construction can be assembled from explicit
certified finite raw geometry and safe-group extension steps:

* start with the empty original raw rectangle on Fin 0, with the
  genuine trivial safe subgroup of its original automorphism group;
* enumerate ALL finite original raw rectangles on canonical Fin n
  carriers (finite raw alphabet);
* at successive stages, preserve the old finite safe group strictly,
  realize ALL old partial original-language maps, and embed the next
  scheduled raw structure;
* pass to the exact directed quotient limits of vertices and finite
  groups, respecting E and EVERY ordered raw colour;
* their limit is countable and ultrahomogeneous, has the FULL finite
  age (arbitrary finite vertex carriers, not merely Fin n), and
  admits one dense locally finite subgroup of its genuine
  original-language automorphism group.

The only algebraic condition in the positive statement is ONE
complete good affine congruence orbit, not global congruence
saturation. No external infinite Fraïssé construction or
HKN EPPA theorem is invoked. The remaining DLF iff and the
exceptional trivial effective-group branch are separate.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

/-- The positive DLF homogeneous-witness theorem in the genuine
original E/R_c language.

Under a complete good affine orbit, there is an actual explicitly
constructed quotient limit M of finite safe raw pairs satisfying:

(1) its vertex carrier is countable;
(2) every finite original raw rectangle on an ARBITRARY finite
    carrier embeds inducedly into M;
(3) every finite original partial isomorphism of M extends
    to an ACTUAL original-language automorphism of M;
(4) Aut_raw(M) has a dense locally finite subgroup, where
    density means exact agreement on each finite vertex set.

The tower itself and all strict finite safe subgroup actions are
returned, rather than assumed as hypotheses. -/
theorem RawDatum.exists_countableHomogeneousDLF_of_completeGoodOrbit
    (d : RawDatum G C)
    (hOrbit : d.HasCompleteGoodOrbit) :
    ∃ (V : ℕ → Type (max u v))
      (hV : ∀ n, Finite (V n)),
      letI : ∀ n, Finite (V n) := hV
      ∃ T : FiniteSafeRawPairTower d V,
        Countable T.VertexLimit ∧
        (∀ (W : Type w) [Fintype W]
          (P : RawRectanglePresentation d W),
          ∃ e : W → T.VertexLimit,
            Function.Injective e ∧
            (∀ x y : W,
              T.limitRawPresentation.part (e x) (e y) ↔ P.part x y) ∧
            (∀ x y : W,
              T.limitRawPresentation.colour (e x) (e y) = P.colour x y)) ∧
        (∀ (F : Finset T.VertexLimit) (p : F → T.VertexLimit),
          Function.Injective p →
          (∀ x y : F,
            T.limitRawPresentation.part (p x) (p y) ↔
              T.limitRawPresentation.part x.val y.val) →
          (∀ x y : F,
            T.limitRawPresentation.colour (p x) (p y) =
              T.limitRawPresentation.colour x.val y.val) →
          ∃ a : T.limitRawPresentation.fullRawAutGroup,
            ∀ x : F, a.val x.val = p x) ∧
        (∃ L : Subgroup (Equiv.Perm T.VertexLimit),
          L ≤ T.limitRawPresentation.fullRawAutGroup ∧
          DenseByFiniteRestrictions T.limitRawPresentation.fullRawAutGroup L ∧
          EveryFinitelyGeneratedSubgroupFinite L) := by
  classical
  let A₀ : FiniteSafePairState d := {
    carrier := ULift.{max u v} (Fin 0)
    finite_carrier := inferInstance
    pair := ((emptyFiniteRaw (d := d)).pullbackRaw ULift.down).trivialSafePair
  }
  obtain ⟨V, hV, T, hConn, _hOld, hFin, hDLF⟩ :=
    exists_universalHomogeneousDLFTower_onFin A₀ hOrbit
  letI : ∀ n, Finite (V n) := hV
  refine ⟨V, hV, T, T.countable_vertexLimit, ?_, ?_, hDLF⟩
  · exact T.limitRawPresentation.inducedFiniteAge_of_canonicalFinAge hFin
  · intro F p hp hPart hColour
    exact T.finiteRawPartialMap_extends_on_limit
      hConn F p hp hPart hColour

end SemigenericEPPA
