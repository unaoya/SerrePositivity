module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeFaceCancellation

/-!
# 最大旗の内部面の符号付き相殺

概要：全ての最大旗の固定した内部面の符号付き和は零である。
方針：隣接する二座標の交換は面を保ち符号を反転する固定点のない対合である。
規約：係数群に二倍の消去は仮定せず、対合で二項ずつ相殺する。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の立方体の基本鎖の境界公式。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：隣接する二座標を交換すると置換符号は負になる。
方針：置換符号の乗法性と互換の符号の計算を使う。
規約：座標は r と r+1 なので異なる。
使われ方：Kerodon 2.5.9（Tag 00SC） の内部面の二項の符号の比較。 -/
lemma cubeSign_swap_trans {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 1)) :
    (Equiv.Perm.sign ((Equiv.swap r.castSucc r.succ).trans σ) : ℤ) =
      -(Equiv.Perm.sign σ : ℤ) := by
  have hr : r.castSucc ≠ r.succ := by
    intro h
    have hv : r.val = r.val + 1 := congrArg Fin.val h
    omega
  rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_swap hr]
  simp

/-- 概要：最大旗の固定した内部面は全置換の符号付き和で相殺する。
方針：隣接交換を対合として有限和の二項ずつの相殺を適用する。
規約：面の値は任意の可換加法群に取れる。
使われ方：HA 1.3.1.16 の基本鎖の境界から内部面を除く。 -/
lemma cubeFlag_internal_sum_eq_zero {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T)
    (r : Fin (n + 1)) {M : Type*} [AddCommGroup M]
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T) _⦋n + 1⦌ → M) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ r.succ.castSucc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans e)))) = 0 := by
  apply Finset.sum_ninvolution (fun σ ↦ (Equiv.swap r.castSucc r.succ).trans σ)
  · intro σ
    have hface := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_face_swap (σ.trans e) r
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ r.succ.castSucc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans e)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ r.succ.castSucc
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (((Equiv.swap r.castSucc r.succ).trans σ).trans e)) at hface
    rw [cubeSign_swap_trans, ← hface, neg_smul, add_neg_cancel]
  · intro σ _ he
    have h := congrArg (fun τ : Equiv.Perm (Fin (n + 2)) ↦ τ r.castSucc) he
    simp only [Equiv.trans_apply, Equiv.swap_apply_left] at h
    have hv : r.val + 1 = r.val := congrArg Fin.val (σ.injective h)
    omega
  · intro σ
    exact Finset.mem_univ _
  · intro σ
    apply Equiv.ext
    intro i
    simp [Equiv.trans_apply]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
