import SemigenericEPPA.Algebra.ExactReplicatedOccupiedCoding
import SemigenericEPPA.Valuations.ReplicatedOccupiedProjection
import SemigenericEPPA.Bridge.OccupiedProjectionFlipSafety

/-!
# One fixed-carrier group action with certified raw flip safety (G=1)

This is the positive geometric assembly of previously certified gates:
(1) a genuinely fixed carrier I × Fin M;
(2) selected old class fibres X_i with |X_i|·t_i=M and injections
    j_i into the PRECHOSEN Fin M;
(3) exact replica coding preserving every part and old copy-zero point;
(4) a strict H-action on all copied vertices, fixing unused parts;
(5) an Option-valued H-equivariant projection from occupied vertices
    to genuine old vertices;
(6) the occupied-only flipped-edge safety theorem.

If the effective group G is a subsingleton, the cross-effective
colours of the fixed witness and those projected from S coincide
automatically. Hence EVERY H-flipped cross-E witness pair has a
literal reversal-fixed raw representative, with no restriction on
the order of h.

This supplies a UNIFORM safe effective action on a prechosen carrier.
It is still a conditional theorem about the classwise sizes, the
chosen H-action on old E-indices, and a fixed effective witness B.
Their construction and the later raw cover and coherent groupoid
assembly remain separate.
-/

namespace SemigenericEPPA

universe u v w z

variable {H : Type u} [Group H]
variable {G : Type v} [Group G] [Subsingleton G]
variable {C : Type w} {S : Type z} {I : Type*}

/-- The canonical embedded old vertex in the globally fixed padded
carrier, using a prescribed injection of each actual occupied class
fibre into the corresponding Fin M. -/
def fixedReplicaOldMap
    (cls : S → I) (M : ℕ)
    (j : ∀ i : ReplicatedOccupiedIndex cls,
      ReplicatedOldFibre cls i → Fin M)
    (x : S) : I × Fin M :=
  (cls x, j ⟨cls x,⟨x,rfl⟩⟩ ⟨x,rfl⟩)

/-- A selected old H-action preserving E and raw colours lifts
HOMOMORPHICALLY to the SAME prechosen fixed carrier I×Fin M.
The lift exactly extends all old vertices, preserves the E/F
geometry, covers the intended quotient-index action, and is safe
for every flipped cross-E pair in the raw sense.

No H-dependent witness carrier, raw-cover baseline, or noncanonical
choice of individual h-lifts is introduced. -/
theorem exists_safeReplicatedFixedCarrierAction
    (d : RawDatum G C)
    (D : EffectiveGeometry d.s S)
    (B : EffectiveGeometry d.s (I × Fin M))
    (cls : S → I)
    (hDpart : ∀ x y : S, D.part x y ↔ cls x = cls y)
    (hBpart : ∀ x y : I × Fin M,
      B.part x y ↔ x.1 = y.1)
    (old : S → S → C)
    (hPhi : ∀ x y : S, ¬D.part x y →
      d.phi (old x y) = D.F x y)
    (hReverse : ∀ x y : S, ¬D.part x y →
      old y x = d.reverse (old x y))
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (hFixed : ∀ (h : H) (i : I),
      (¬∃ x : S, cls x = i) → iota h i = i)
    (hRaw : ∀ (h : H) (x y : S), ¬D.part x y →
      old (rho h x) (rho h y) = old x y)
    (t : I → ℕ)
    (ht : ∀ (h : H) (i : I), t (iota h i) = t i)
    (hfin : ∀ i : ReplicatedOccupiedIndex cls,
      Fintype (ReplicatedOldFibre cls i))
    (hpos : ∀ i : ReplicatedOccupiedIndex cls, 0 < t i.val)
    (hsize : ∀ i : ReplicatedOccupiedIndex cls,
      (@Fintype.card (ReplicatedOldFibre cls i) (hfin i)) *
        t i.val = M)
    (j : ∀ i : ReplicatedOccupiedIndex cls,
      ReplicatedOldFibre cls i → Fin M)
    (hj : ∀ i : ReplicatedOccupiedIndex cls,
      Function.Injective (j i)) :
    ∃ action : H →* Equiv.Perm (I × Fin M),
      (∀ (h : H) (x : S),
        action h (fixedReplicaOldMap cls M j x) =
          fixedReplicaOldMap cls M j (rho h x)) ∧
      (∀ (h : H) (x : I × Fin M),
        (action h x).1 = iota h x.1) ∧
      (∀ (h : H) (x y : I × Fin M),
        B.part (action h x) (action h y) ↔ B.part x y) ∧
      (∀ (h : H) (x y : I × Fin M),
        ¬B.part x y →
        B.F (action h x) (action h y) = B.F x y) ∧
      (∀ (h : H) (x y : I × Fin M),
        ¬B.part x y → action h x = y → action h y = x →
        ∃ c : C, d.phi c = B.F x y ∧ d.reverse c = c) := by
  classical
  let occupied : I → Prop := fun i => ∃ x : S, cls x = i
  let hposS : ∀ x : S, 0 < t (cls x) :=
    fun x => hpos ⟨cls x,⟨x,rfl⟩⟩
  obtain ⟨e, hCoding, hOld⟩ :=
    exists_exactReplicatedOccupiedCoding cls t M hfin hpos hsize j hj
  let action : H →* Equiv.Perm (I × Fin M) :=
    replicatedFixedCarrierGroupAction rho iota cls hCls t ht
      Prod.fst occupied e
  have hIdx (h : H) (x : I × Fin M) :
      (action h x).1 = iota h x.1 :=
    replicatedFixedCarrierGroupAction_class rho iota cls hCls
      t ht Prod.fst occupied hFixed e hCoding h x
  let proj : (I × Fin M) → Option S :=
    replicatedOccupiedProjection cls t Prod.fst occupied e
  have hSome (x : I × Fin M) (hx : occupied x.1) :
      ∃ a : S, proj x = some a :=
    replicatedOccupiedProjection_some cls t Prod.fst occupied e x hx
  have hProj (h : H) (x : I × Fin M) :
      proj (action h x) = Option.map (rho h) (proj x) :=
    replicatedOccupiedProjection_equivariant rho iota cls
      hCls t ht Prod.fst occupied e h x
  have hProjClass (x : I × Fin M) (a : S)
      (ha : proj x = some a) : x.1 = cls a := by
    by_cases hx : occupied x.1
    · have hp : (e.symm ⟨x, hx⟩).1 = a := by
        change (if hw : occupied x.1 then
            some (e.symm ⟨x, hw⟩).1 else none) = some a at ha
        simp only [dif_pos hx] at ha
        exact Option.some.inj ha
      have he : (e (e.symm ⟨x,hx⟩)).val = x :=
        congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
      calc
        x.1 = (e (e.symm ⟨x,hx⟩)).val.1 := by rw [he]
        _ = cls (e.symm ⟨x,hx⟩).1 := hCoding _
        _ = cls a := congrArg cls hp
    · have hn : proj x = none := by
        simp [proj, replicatedOccupiedProjection, hx]
      rw [hn] at ha
      cases ha
  have hCross (x y : I × Fin M) (a b : S)
      (ha : proj x = some a) (hb : proj y = some b)
      (hxy : ¬B.part x y) : ¬D.part a b := by
    intro hab
    apply hxy
    apply (hBpart x y).mpr
    calc
      x.1 = cls a := hProjClass x a ha
      _ = cls b := (hDpart a b).mp hab
      _ = y.1 := (hProjClass y b hb).symm
  have hColour (x y : I × Fin M) (a b : S)
      (_ha : proj x = some a) (_hb : proj y = some b)
      (_hxy : ¬B.part x y) :
      B.F x y = D.F a b :=
    Subsingleton.elim _ _
  have hSafe :=
    allFlippedCrossPairs_safe_of_occupiedProjection
      d D B old hPhi hReverse rho action iota
        Prod.fst occupied hBpart hIdx hFixed proj
          hSome hProj hCross hColour hRaw
  refine ⟨action, ?_, hIdx, ?_, ?_, hSafe⟩
  · intro h x
    exact replicatedFixedCarrierGroupAction_old
      rho iota cls hCls t ht hposS Prod.fst occupied
      e (fixedReplicaOldMap cls M j) hOld h x
  · intro h x y
    rw [hBpart (action h x) (action h y), hBpart x y,
      hIdx h x, hIdx h y]
    exact ⟨fun heq => (iota h).injective heq,
      fun heq => congrArg (iota h) heq⟩
  · intro h x y hxy
    exact Subsingleton.elim _ _

end SemigenericEPPA
