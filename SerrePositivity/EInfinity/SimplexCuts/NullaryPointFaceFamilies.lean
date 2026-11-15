module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointFaceData
public import SerrePositivity.EInfinity.SimplexCuts.NullaryRawPositions
public import SerrePositivity.EInfinity.IntervalCuts.InsertionFamilies

/-!
# 一点削除の元の全出力順序での面の族

Berger–Fresse §2.2.6・§3.1、M14 L12a、報告 §350。
元のoperadInsertionEquivと残り色の指定番号を使って全族を厳密に比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ一点削除の全指定面の族は元の空語代入の順序の族（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_faceFamily_relabel {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hpoint : hi s p = lo s p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) :
    (fun c : Fin r => (⟨outputDegree (nullaryPointEraseCut s p) w c,
      vertices (nullaryPointEraseCut s p) w c⟩ : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1))) =
      IntervalCuts.insertionFamily
        (fun a => (⟨outputDegree s v a, vertices s v a⟩ :
          Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)))
        (fun j : Fin 0 => Fin.elim0 j) k := by
  funext c
  obtain ⟨z, hz⟩ := (operadInsertionEquiv r 0 k).symm.surjective c
  rw [← hz]
  cases z with
  | inl a =>
    have H := nullaryPointEraseCut_faceData_relabel s v w p k hp hpoint hv
      (BarrattEccles.remainingPosition r 0 k a)
    rw [succAbove_remainingPosition_nullary] at H
    simpa only [IntervalCuts.insertionFamily, BarrattEccles.remainingPosition,
      Equiv.apply_symm_apply] using H
  | inr a => exact Fin.elim0 a

end SerrePositivity.EInfinity.SimplexCuts
