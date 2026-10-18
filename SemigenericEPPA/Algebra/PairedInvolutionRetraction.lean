import Mathlib.Logic.Function.Basic

/-!
# Equivariant decoding on a two-orbit of exchanged sorts

When effective reversal sends g to a distinct effective colour s(g),
the raw fibres C_g and C_s(g) are exchanged bijectively. There is
no fixed-point issue: one chooses a left inverse of the injected
fibre at g and transports it to the opposite fibre by reversal.

This abstract theorem makes that operation precise. Let B₁ and B₂
be linked by an equivalence R, let L carry an involution τ, and
suppose injections into L satisfy e₂(R b)=τ(e₁ b).

Then there exist left-inverse decoders q₁,q₂ which commute with
the exchange and τ in BOTH directions. No finiteness or order is
needed on any of these types (only nonemptiness of B₁).

This is exactly the missing nonfixed-effective-colour decoder step
for the uniform affine raw residual code.
-/

namespace SemigenericEPPA

universe u v w

variable {B₁ : Type u} {B₂ : Type v} {L : Type w}
variable [Nonempty B₁]

/-- Equivariant left inverses of two encoders whose fibres are
exchanged by an equivalence and whose coefficient space has
an involution. -/
theorem exists_equivariantPairedRetraction
    (R : B₁ ≃ B₂)
    (τ : L → L) (hτ : Function.Involutive τ)
    (e₁ : B₁ → L) (e₂ : B₂ → L)
    (he₁ : Function.Injective e₁)
    (hequiv : ∀ b : B₁, e₂ (R b) = τ (e₁ b)) :
    ∃ (q₁ : L → B₁) (q₂ : L → B₂),
      (∀ b : B₁, q₁ (e₁ b) = b) ∧
      (∀ b : B₂, q₂ (e₂ b) = b) ∧
      (∀ l : L, q₂ (τ l) = R (q₁ l)) ∧
      (∀ l : L, q₁ (τ l) = R.symm (q₂ l)) := by
  classical
  let b₀ : B₁ := Classical.choice inferInstance
  let q₁ : L → B₁ := fun l =>
    if h : ∃ b : B₁, e₁ b = l then Classical.choose h else b₀
  have hq₁ (b : B₁) : q₁ (e₁ b) = b := by
    have h : ∃ b' : B₁, e₁ b' = e₁ b := ⟨b, rfl⟩
    change (if h : ∃ b' : B₁, e₁ b' = e₁ b then
      Classical.choose h else b₀) = b
    rw [dif_pos h]
    exact he₁ (Classical.choose_spec h)
  let q₂ : L → B₂ := fun l => R (q₁ (τ l))
  have hq₂ (b : B₂) : q₂ (e₂ b) = b := by
    let a : B₁ := R.symm b
    have hb : e₂ b = τ (e₁ a) := by
      calc
        e₂ b = e₂ (R a) :=
          congrArg e₂ (R.apply_symm_apply b).symm
        _ = τ (e₁ a) := hequiv a
    change R (q₁ (τ (e₂ b))) = b
    rw [hb, hτ, hq₁, R.apply_symm_apply]
  refine ⟨q₁, q₂, hq₁, hq₂, ?_, ?_⟩
  · intro l
    change R (q₁ (τ (τ l))) = R (q₁ l)
    rw [hτ]
  · intro l
    change q₁ (τ l) = R.symm (R (q₁ (τ l)))
    rw [R.symm_apply_apply]

end SemigenericEPPA
