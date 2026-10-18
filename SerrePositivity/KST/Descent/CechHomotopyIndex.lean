module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Čech 細分ホモトピーの有限添字

## 概要
二つの比較射の切替位置と重複する座標を、面射・退化射の全恒等式について検査する。

## 方針
元の座標と比較射のタグの組を使い、有限順序集合の算術へ還元する。

## 規約
タグ 0 は最初の比較、タグ 1 は次の比較。元のスキームの作用とは無関係。

## 使われ方
論文 補題 3.2 を Čech 計算に置換する際の細分比較のホモトピー。
-/

@[expose] public section

namespace SerrePositivity.KST.Descent

/-- 概要：Čech ホモトピーの出力座標と比較射のタグ（論文 補題 3.2）。
方針：切替座標を一度重複し、その左右で二つの比較射を使う。
規約：タグは 0 または 1。
使われ方：実際の Čech ホモトピーの各射影。 -/
def cechMixIndex {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) : Fin (n + 1) × ℕ :=
  (i.predAbove j, if j ≤ i.castSucc then 0 else 1)

private theorem predAbove_val {n : ℕ} (i : Fin n) (j : Fin (n + 1)) :
    (i.predAbove j).val = if i.val < j.val then j.val - 1 else j.val := by
  simp only [Fin.predAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

private theorem succAbove_val {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (i.succAbove j).val = if j.val < i.val then j.val else j.val + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

/-- 概要：最初の面は第二の比較になる（論文 補題 3.2）。
方針：零番目を除いて切替座標を計算する。
規約：第二の比較のタグは 1。
使われ方：細分ホモトピーの終点。 -/
theorem cechMixIndex_zero {n : ℕ} (j : Fin (n + 1)) :
    cechMixIndex (0 : Fin (n + 1)) ((0 : Fin (n + 2)).succAbove j) = (j, 1) := by
  simp [cechMixIndex, Fin.predAbove, Fin.succAbove]

/-- 概要：最後の面は第一の比較になる（論文 補題 3.2）。
方針：最後の座標を除いて切替座標を計算する。
規約：第一の比較のタグは 0。
使われ方：細分ホモトピーの始点。 -/
theorem cechMixIndex_last {n : ℕ} (j : Fin (n + 1)) :
    cechMixIndex (Fin.last n) ((Fin.last (n + 1)).succAbove j) = (j, 0) := by
  simp [cechMixIndex, Fin.succAbove_last_apply, Fin.predAbove_of_le_castSucc,
    Fin.le_last]

/-- 概要：切替位置より前の面射との添字の整合性（論文 補題 3.2）。
方針：座標と比較タグをそれぞれ有限順序集合の算術で検査する。
規約：ホモトピーの第三の面の恒等式の添字。
使われ方：細分比較の実際のホモトピー。 -/
theorem cechMixIndex_face_before {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) (k : Fin (n + 2)) :
    cechMixIndex j.succ (i.castSucc.succAbove k) =
      (i.succAbove (cechMixIndex j k).1, (cechMixIndex j k).2) := by
  apply Prod.ext
  · apply Fin.ext
    simp only [cechMixIndex, predAbove_val, succAbove_val, Fin.le_def,
      Fin.val_castSucc, Fin.val_succ] at *
    split_ifs at * <;> omega
  · simp only [cechMixIndex, succAbove_val, Fin.le_def,
      Fin.val_castSucc, Fin.val_succ] at *
    split_ifs at * <;> omega

/-- 概要：切替位置上の二つの面射の添字は一致（論文 補題 3.2）。
方針：重複した座標のどちらを除くかによらないことを検査する。
規約：タグも一致させる。
使われ方：細分ホモトピーの中央の面の恒等式。 -/
theorem cechMixIndex_face_middle {n : ℕ} (j : Fin (n + 1)) (k : Fin (n + 2)) :
    cechMixIndex j.succ (j.castSucc.succ.succAbove k) =
      cechMixIndex j.castSucc (j.castSucc.succ.succAbove k) := by
  apply Prod.ext
  · apply Fin.ext
    simp only [cechMixIndex, predAbove_val, succAbove_val, Fin.le_def,
      Fin.val_castSucc, Fin.val_succ] at *
    split_ifs at * <;> omega
  · simp only [cechMixIndex, succAbove_val, Fin.le_def,
      Fin.val_castSucc, Fin.val_succ] at *
    split_ifs at * <;> omega

/-- 概要：切替位置より後の面射との添字の整合性（論文 補題 3.2）。
方針：除かれる座標が切替位置より後にある場合を検査する。
規約：元の面射の添字を保持する。
使われ方：細分ホモトピーの後半の面の恒等式。 -/
theorem cechMixIndex_face_after {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) (k : Fin (n + 2)) :
    cechMixIndex j.castSucc (i.succ.succAbove k) =
      (i.succAbove (cechMixIndex j k).1, (cechMixIndex j k).2) := by
  apply Prod.ext
  · apply Fin.ext
    simp only [cechMixIndex, predAbove_val, succAbove_val, Fin.lt_def, Fin.le_def,
      Fin.val_castSucc, Fin.val_succ] at *
    split_ifs at * <;> omega
  · simp only [cechMixIndex, succAbove_val, Fin.lt_def, Fin.le_def,
      Fin.val_castSucc, Fin.val_succ] at *
    split_ifs at * <;> omega

/-- 概要：切替位置以前の退化射との添字の整合性（論文 補題 3.2）。
方針：二つの重複する座標の順序を算術で検査する。
規約：退化射の添字が切替位置以下の場合。
使われ方：細分ホモトピーの退化射の恒等式。 -/
theorem cechMixIndex_degeneracy_before {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j)
    (k : Fin (n + 3)) :
    cechMixIndex j (i.castSucc.predAbove k) =
      (i.predAbove (cechMixIndex j.succ k).1, (cechMixIndex j.succ k).2) := by
  apply Prod.ext
  · apply Fin.ext
    simp only [cechMixIndex, predAbove_val, Fin.le_def,
      Fin.val_castSucc, Fin.val_succ] at *
    split_ifs at * <;> omega
  · simp only [cechMixIndex, predAbove_val, Fin.le_def,
      Fin.val_castSucc, Fin.val_succ] at *
    split_ifs at * <;> omega

/-- 概要：切替位置以後の退化射との添字の整合性（論文 補題 3.2）。
方針：重複する座標が切替位置以後にある場合を検査する。
規約：切替位置が退化射の添字以下の場合。
使われ方：細分ホモトピーの後半の退化射の恒等式。 -/
theorem cechMixIndex_degeneracy_after {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i)
    (k : Fin (n + 3)) :
    cechMixIndex j (i.succ.predAbove k) =
      (i.predAbove (cechMixIndex j.castSucc k).1, (cechMixIndex j.castSucc k).2) := by
  apply Prod.ext
  · apply Fin.ext
    simp only [cechMixIndex, predAbove_val, Fin.le_def,
      Fin.val_castSucc, Fin.val_succ] at *
    split_ifs at * <;> omega
  · simp only [cechMixIndex, predAbove_val, Fin.le_def,
      Fin.val_castSucc, Fin.val_succ] at *
    split_ifs at * <;> omega

end SerrePositivity.KST.Descent
