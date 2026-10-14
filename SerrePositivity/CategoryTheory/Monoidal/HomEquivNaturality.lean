module

public import Mathlib.Logic.Equiv.Basic

/-! # 二つのHom同値の自然性から得る第三の同値の自然性 -/

@[expose] public section

universe u₁ u₂ u₃ u₁' u₂' u₃'

namespace SerrePositivity.HomEquivNaturality

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  {A' : Type u₁'} {B' : Type u₂'} {C' : Type u₃'}
  (q : A ≃ B) (q' : A' ≃ B') (r : A ≃ C) (r' : A' ≃ C')
  (f : A → A') (g : B → B') (h : C → C')

/-- 共通の原変数を介して得た同値の自然性の等式。 -/
def derivedLaw (y : B) : Prop := (q'.symm.trans r') (g y) = h ((q.symm.trans r) y)

/-- 共通の原変数からの二つの同値の自然性を、残りの二つの型の同値へ送る。 -/
lemma derived (hq : ∀ x, q' (f x) = g (q x)) (hr : ∀ x, r' (f x) = h (r x))
    (y : B) : derivedLaw q q' r r' g h y := by
  have hx := hq (q.symm y)
  rw [q.apply_symm_apply] at hx
  have hi : q'.symm (g y) = f (q.symm y) := (q'.symm_apply_eq).mpr hx.symm
  unfold derivedLaw
  rw [Equiv.trans_apply, Equiv.trans_apply, hi]
  exact hr (q.symm y)

end SerrePositivity.HomEquivNaturality
