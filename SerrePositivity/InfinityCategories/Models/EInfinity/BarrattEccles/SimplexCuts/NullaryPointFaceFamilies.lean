module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPointFaceData
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryRawPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InsertionFamilies

/-!
模型。文献の定義との比較は後で
# 一点削除の元の全出力順序での面の族

Berger–Fresse §2.2.6・§3.1、M14 L12a、報告 §350。
元のoperadInsertionEquivと残り色の指定番号を使って全族を厳密に比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 同じ一点削除の全指定面の族は元の空語代入の順序の族（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_faceFamily_relabel {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1) (m + 2)) (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1))
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hpoint : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) :
    (fun c : Fin r => (⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) w c,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) w c⟩ : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily
        (fun a => (⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s v a⟩ :
          Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)))
        (fun j : Fin 0 => Fin.elim0 j) k := by
  funext c
  obtain ⟨z, hz⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv r 0 k).symm.surjective c
  rw [← hz]
  cases z with
  | inl a =>
    have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut_faceData_relabel s v w p k hp hpoint hv
      (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition r 0 k a)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.succAbove_remainingPosition_nullary] at H
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily, _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition,
      Equiv.apply_symm_apply] using H
  | inr a => exact Fin.elim0 a

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
