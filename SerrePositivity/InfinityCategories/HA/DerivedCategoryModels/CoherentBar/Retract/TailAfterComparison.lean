module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.TailDegeneracyNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegeneracyOperators
/-!
概要：加法表示した tail を元の bar の tail ラベルと同定する。
方針：次数の等号を eqToHom に明示し、presheaf の輸送が元の単体と異種等号で一致することを使う。
規約：元の tail の次数と端点を変更せず、自然数の減法による輸送も保持する。
使われ方：退化との厳密な可換式を、元の prefix 列の tail に適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory SSet
open scoped _root_.Simplicial

lemma dgCoherentBarTailOrder_after (k n : ℕ) :
    SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder (k + n) k (by omega)) =
      eqToHom (congrArg SimplexCategory.mk (Nat.add_sub_cancel_left k n)) ≫
        SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarTailAfterOrder k n) := by
  ext a
  change k + a.val = k +
    ((eqToHom (congrArg SimplexCategory.mk (Nat.add_sub_cancel_left k n))).toOrderHom a).val
  rw [SimplexCategory.eqToHom_toOrderHom]
  rfl

variable {I : SSet.{u}}

private lemma map_eqToHom_heq {m n : ℕ} (h : m = n) (s : I _⦋n⦌) :
    HEq (I.map (eqToHom (congrArg SimplexCategory.mk h)).op s) s := by
  cases h
  simp

lemma dgCoherentBarTail_after (k n : ℕ) (s : I _⦋k + n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s k (by omega) = ⟨n, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarTailAfter k n s⟩ := by
  apply Sigma.ext (Nat.add_sub_cancel_left k n)
  have h := congrArg (fun f => I.map f.op s) (dgCoherentBarTailOrder_after k n)
  simp only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] at h
  exact (heq_of_eq h).trans (map_eqToHom_heq (Nat.add_sub_cancel_left k n) _)

lemma dgCoherentBarTail_degeneracy_after (k n : ℕ) (j : Fin (n + 1))
    (s : I _⦋k + n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail (I.σ (⟨k + j.val, by
      change k + j.val < k + n + 1
      omega⟩ : Fin (k + n + 1)) s) k (by omega) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracy (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarTailAfter k n s) j := by
  have h := dgCoherentBarTail_after k (n + 1)
    (I.σ (⟨k + j.val, by omega⟩ : Fin (k + n + 1)) s)
  have hh := congrArg (fun t => (⟨n + 1, t⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarTailAfter_degeneracy k n j s)
  exact h.trans hh

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
