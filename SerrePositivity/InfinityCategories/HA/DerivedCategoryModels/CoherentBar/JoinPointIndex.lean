module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinCuts
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedIndex
/-!
概要：パラメーターが一点の join 添字と、既存の末端付き添字を同定する。
方針：左右の区間で所属を比較し、全頂点の昇順列挙は恒等射であることを使う。
規約：既存の withLast と native 単体の公開型を保持する。
使われ方：混合成分の因数分解を native 単体の HA 削除・切断成分へ適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory
open scoped _root_.Simplicial

lemma dgCoherentBarJoinSubset_point {n : ℕ} (K : Finset (Fin (n + 1))) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K (Finset.univ : Finset (Fin 1)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast K := by
  change K.image Fin.castSucc ∪
    (Finset.univ : Finset (Fin 1)).image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n 0) = _
  have he : (Finset.univ : Finset (Fin 1)) = {0} := Finset.univ_unique
  rw [he, Finset.image_singleton, Finset.union_singleton]
  rfl

lemma dgCoherentBarUniv_orderHom (n : ℕ) :
    SimplexCategory.mkHom
      ((Finset.univ : Finset (Fin (n + 1))).orderEmbOfFin (by simp)).toOrderHom = 𝟙 ⦋n⦌ := by
  have he : (fun i : Fin (n + 1) => i) =
      (Finset.univ : Finset (Fin (n + 1))).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique (by simp) (fun _ => Finset.mem_univ _) strictMono_id
  ext i : 3
  exact congrFun he.symm i

lemma dgCoherentBarWithLast_erase {n : ℕ} (K : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (K.erase j) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast K).erase j.castSucc := by
  rw [← dgCoherentBarJoinSubset_point, ← dgCoherentBarJoinSubset_point,
    ← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_erase_left]
  rfl

lemma dgCoherentBarWithLast_filter_left_le {n : ℕ}
    (K : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (K.filter (j ≤ ·)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast K).filter (j.castSucc ≤ ·) := by
  rw [← dgCoherentBarJoinSubset_point, ← dgCoherentBarJoinSubset_point,
    ← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_filter_left_le]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
