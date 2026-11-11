module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeEvaluation

/-!
# 隣接交換による最大旗の内部面の一致

概要：二つの隣接座標を交換した最大旗は、その間の頂点を削除すると同じ面になる。
方針：残る頂点の番号は交換された二座標の間の番号を避けることを使う。
規約：座標の番号付けの向きを保ったまま隣接交換を行う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の基本鎖の内部面の相殺。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：隣接座標を交換した二つの最大旗の共通の内部面は一致する。
方針：交換される座標以外は変わらず、交換される二座標は残る全頂点で同時に属する。
規約：二つの最大旗の間の内部頂点を削除する。
使われ方：Kerodon 2.5.9（Tag 00SC） の置換を対にした内部面の消去。 -/
lemma cubeFlag_face_swap {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T) (r : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ r.succ.castSucc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ r.succ.castSucc
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag ((Equiv.swap r.castSucc r.succ).trans e)) := by
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  apply Set.ext
  intro a
  change (e.symm a).val < (r.succ.castSucc.succAbove t).val ↔
    ((Equiv.swap r.castSucc r.succ) (e.symm a)).val < (r.succ.castSucc.succAbove t).val
  have hne : (r.succ.castSucc.succAbove t).val ≠ r.val + 1 := by
    intro h
    apply Fin.succAbove_ne r.succ.castSucc t
    exact Fin.ext h
  by_cases ha : e.symm a = r.castSucc
  · rw [ha, Equiv.swap_apply_left]
    change r.val < (r.succ.castSucc.succAbove t).val ↔
      r.val + 1 < (r.succ.castSucc.succAbove t).val
    omega
  by_cases hb : e.symm a = r.succ
  · rw [hb, Equiv.swap_apply_right]
    change r.val + 1 < (r.succ.castSucc.succAbove t).val ↔
      r.val < (r.succ.castSucc.succAbove t).val
    omega
  rw [Equiv.swap_apply_of_ne_of_ne ha hb]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
