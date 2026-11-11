module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeCoordinateFaces

/-!
# 置換の先頭・末尾と最大旗の外側の面

概要：最大旗の外側の二面を、固定座標を含む面と含まない面の最大旗に同定する。
方針：先頭座標を指定する置換の分解と、その巡回移動による末尾版を使う。
規約：残る座標は succAbove の順序で番号付けする。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の立方体の基本鎖の外側境界。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：最後の座標を指定した置換を作る。
方針：最初の座標を指定する置換を巡回移動する。
規約：castSucc j は i.succAbove (σ j)、最後の点は i に送る。
使われ方：Kerodon 2.5.9（Tag 00SC） の座標0面に対応する旗の添字。 -/
def cubeLastPermutation {n : ℕ} (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) :=
  (finRotate (n + 2)).trans (Equiv.Perm.decomposeFin'Symm i σ)

/-- 概要：末尾指定の置換は前の全座標を指定した残りの順序で送る。
方針：finRotate の非終点での計算を使う。
規約：番号 j は castSucc で元の番号に埋め込む。
使われ方：Kerodon 2.5.9（Tag 00SC） の最後の面の計算。 -/
lemma cubeLastPermutation_castSucc {n : ℕ} (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    cubeLastPermutation i σ j.castSucc = i.succAbove (σ j) := by
  have hr : finRotate (n + 2) j.castSucc = j.succ := finRotate_of_lt j.isLt
  unfold cubeLastPermutation
  rw [Equiv.trans_apply, hr]
  rfl

/-- 概要：末尾指定の置換の最後の値は指定座標である。
方針：巡回移動の最後の値が零となることを使う。
規約：最後の点は Fin.last で表す。
使われ方：Kerodon 2.5.9（Tag 00SC） の座標0面の固定座標。 -/
lemma cubeLastPermutation_last {n : ℕ} (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 1))) : cubeLastPermutation i σ (Fin.last (n + 1)) = i := by
  simp [cubeLastPermutation, Equiv.trans_apply]

/-- 概要：末尾指定の置換の指定座標の逆像は最後の点である。
方針：置換を適用して最後の値の計算へ戻す。
規約：逆写像の値として述べる。
使われ方：Kerodon 2.5.9（Tag 00SC） の最後の面の所属の検査。 -/
lemma cubeLastPermutation_symm_fixed {n : ℕ} (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (cubeLastPermutation i σ).symm i = Fin.last (n + 1) := by
  apply (cubeLastPermutation i σ).injective
  rw [Equiv.apply_symm_apply, cubeLastPermutation_last]

/-- 概要：末尾指定の置換の残りの座標の逆像は元の番号の castSucc である。
方針：置換を適用して前の座標の値の計算へ戻す。
規約：残りの番号は σ で並べたものを使う。
使われ方：Kerodon 2.5.9（Tag 00SC） の最後の面の最大旗の比較。 -/
lemma cubeLastPermutation_symm_succAbove {n : ℕ} (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    (cubeLastPermutation i σ).symm (i.succAbove (σ j)) = j.castSucc := by
  apply (cubeLastPermutation i σ).injective
  rw [Equiv.apply_symm_apply, cubeLastPermutation_castSucc]

/-- 概要：先頭を指定した置換の最大旗の零番目の面はその座標の1面の旗である。
方針：固定座標と succAbove の像の座標で所属を場合分けする。
規約：残る立方体の旗は σ と ULift の標準同値で番号付けする。
使われ方：HA 1.3.1.16 の基本鎖の最初の面の座標面への移送。 -/
lemma cubeFlag_face_first {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T)
    (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag ((Equiv.Perm.decomposeFin'Symm i σ).trans e)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans Equiv.ulift.symm)) := by
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  apply Set.ext
  intro a
  obtain ⟨q, rfl⟩ := e.surjective a
  change ((Equiv.Perm.decomposeFin'Symm i σ).symm (e.symm (e q))).val <
    ((0 : Fin (n + 3)).succAbove t).val ↔
      e q ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceOrder e i true ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans Equiv.ulift.symm)).obj t)
  rw [e.symm_apply_apply, Fin.succAbove_zero]
  by_cases hq : q = i
  · subst q
    rw [Equiv.Perm.decomposeFin'Symm_symm_eq_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceOrder_mem_fixed]
    simp
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hq
    obtain ⟨b, rfl⟩ := σ.surjective j
    rw [← hj, Equiv.Perm.decomposeFin'Symm_symm_succAbove, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceOrder_mem_succAbove]
    change b.val + 1 < t.val + 1 ↔ (σ.symm (σ b)).val < t.val
    rw [σ.symm_apply_apply]
    omega

/-- 概要：末尾を指定した置換の最大旗の最後の面はその座標の0面の旗である。
方針：固定座標は最後の頂点で初めて入り、それ以外の座標の逆像は元の番号である。
規約：固定座標を含まない面を取る。
使われ方：HA 1.3.1.16 の基本鎖の最後の面の座標面への移送。 -/
lemma cubeFlag_face_last {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T)
    (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag ((cubeLastPermutation i σ).trans e)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans Equiv.ulift.symm)) := by
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  apply Set.ext
  intro a
  obtain ⟨q, rfl⟩ := e.surjective a
  change ((cubeLastPermutation i σ).symm (e.symm (e q))).val <
    ((Fin.last (n + 2)).succAbove t).val ↔
      e q ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceOrder e i false ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans Equiv.ulift.symm)).obj t)
  rw [e.symm_apply_apply, Fin.succAbove_last]
  by_cases hq : q = i
  · subst q
    rw [cubeLastPermutation_symm_fixed, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceOrder_mem_fixed]
    simp only [Bool.false_eq_true, iff_false]
    change ¬ n + 1 < t.val
    have ht : t.val < n + 2 := t.isLt
    omega
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hq
    obtain ⟨b, rfl⟩ := σ.surjective j
    rw [← hj, cubeLastPermutation_symm_succAbove, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceOrder_mem_succAbove]
    change b.val < t.val ↔ (σ.symm (σ b)).val < t.val
    rw [σ.symm_apply_apply]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
