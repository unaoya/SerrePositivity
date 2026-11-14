module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Faces.DGCoherentBarCuts
/-!
概要：重複頂点より前の切断は、残りの tail の退化写像と厳密に可換する。
方針：長さを加法表示した tail の順序写像を使い、二つの predAbove を各場合で比較する。
規約：元の単体の全パラメーターを保持する。次数の等号を省略したラベル置換をしない。
使われ方：正規化境界で prefix 係数の後に現れる退化 tail の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory SSet
open scoped _root_.Simplicial

def dgCoherentBarTailAfterOrder (k n : ℕ) : Fin (n + 1) →o Fin (k + n + 1) where
  toFun a := ⟨k + a.val, by omega⟩
  monotone' := fun _ _ h => Nat.add_le_add_left h k

lemma dgCoherentBarTailAfterOrder_degeneracy (k n : ℕ) (j : Fin (n + 1)) :
    SimplexCategory.mkHom (dgCoherentBarTailAfterOrder k (n + 1)) ≫
      SimplexCategory.σ ⟨k + j.val, by change k + j.val < k + n + 1; omega⟩ =
    SimplexCategory.σ j ≫ SimplexCategory.mkHom (dgCoherentBarTailAfterOrder k n) := by
  ext a
  change ((⟨k + j.val, by change k + j.val < k + n + 1; omega⟩ : Fin (k + n + 1)).predAbove
    (dgCoherentBarTailAfterOrder k (n + 1) a)).val = k + (j.predAbove a).val
  by_cases h : a.val ≤ j.val
  · rw [Fin.predAbove_of_le_castSucc j a h,
      Fin.predAbove_of_le_castSucc _ _ (by change k + a.val ≤ k + j.val; omega)]
    rfl
  · rw [Fin.predAbove_of_castSucc_lt j a (by change j.val < a.val; omega),
      Fin.predAbove_of_castSucc_lt _ _ (by change k + j.val < k + a.val; omega)]
    simp only [Fin.val_pred, dgCoherentBarTailAfterOrder, OrderHom.coe_mk]
    omega

variable {I : SSet.{u}}

def dgCoherentBarTailAfter (k n : ℕ) (s : I _⦋k + n⦌) : I _⦋n⦌ :=
  I.map (SimplexCategory.mkHom (dgCoherentBarTailAfterOrder k n)).op s

lemma dgCoherentBarTailAfter_degeneracy (k n : ℕ) (j : Fin (n + 1)) (s : I _⦋k + n⦌) :
    dgCoherentBarTailAfter k (n + 1) (I.σ ⟨k + j.val, by change k + j.val < k + n + 1; omega⟩ s) =
      I.σ j (dgCoherentBarTailAfter k n s) := by
  have h := congrArg (fun f => I.map f.op s)
    (dgCoherentBarTailAfterOrder_degeneracy k n j)
  simp only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] at h
  change I.map (SimplexCategory.mkHom (dgCoherentBarTailAfterOrder k (n + 1))).op
      (I.map (SimplexCategory.σ (⟨k + j.val, by omega⟩ : Fin (k + n + 1))).op s) =
    I.map (SimplexCategory.σ j).op
      (I.map (SimplexCategory.mkHom (dgCoherentBarTailAfterOrder k n)).op s)
  convert h using 1

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
