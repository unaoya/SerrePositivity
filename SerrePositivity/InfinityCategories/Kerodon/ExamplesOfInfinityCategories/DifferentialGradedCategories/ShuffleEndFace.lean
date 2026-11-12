module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShufflePureFace

/-!
# shuffle の先頭と末尾の面

概要：先頭または末尾に挿入したステップを削除する面を、対応する因子の端の面に同定する。
方針：先頭の前半ステップ数を直接計算し、末尾では一般の挿入公式を使う。
規約：KST Construction A.5 の標準 shuffle。
使われ方：shuffle の鎖写像性の境界の端点の項。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped Simplicial

/-- 概要：先頭の挿入を飛ばすと、既存水平ステップの前半の濃度は保たれる。
方針：両方の番号が一つ増えるため前後関係は変わらない。
規約：KST A.5。使われ方：先頭の二種類の挿入の座標の共通部分。 -/
lemma shuffleInsertion_zero_prefix_card {n : ℕ} (s : Finset (Fin n)) (x : Fin (n + 1)) :
    ((s.map (0 : Fin (n + 1)).succAboveEmb).filter
      (fun j : Fin (n + 1) ↦ (j : ℕ) < (x.succ : ℕ))).card =
      (s.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))).card := by
  rw [Finset.filter_map, Finset.card_map]
  congr 1

/-- 概要：先頭の水平挿入は最初の面に沿って第一座標を常に一つ増やす。
方針：新しい零番目の水平ステップを全ての正の前半へ加える。
規約：KST A.5。使われ方：第一因子の零番目の面。 -/
lemma ShuffleIndex.insertHorizontal_zero_left {p n : ℕ} (s : ShuffleIndex p n)
    (x : Fin (n + 1)) :
    ((s.insertHorizontal 0).left.toOrderHom x.succ : ℕ) = (s.left.toOrderHom x : ℕ) + 1 := by
  rw [ShuffleIndex.left_apply, ShuffleIndex.left_apply]
  change ((insert 0 (s.val.map (0 : Fin (n + 1)).succAboveEmb)).filter
    (fun j : Fin (n + 1) ↦ (j : ℕ) < (x.succ : ℕ))).card = _
  rw [Finset.filter_insert, ite_eq_left (by change 0 < (x : ℕ) + 1; omega),
    Finset.card_insert_of_notMem (by
      intro h
      exact shuffleInsertion_not_mem s.val 0 (Finset.mem_filter.mp h).1),
    shuffleInsertion_zero_prefix_card]

/-- 概要：先頭の垂直挿入は最初の面に沿って第一座標を保つ。
方針：新しいステップを水平集合に加えない。
規約：KST A.5。使われ方：第二因子の零番目の面の第一成分。 -/
lemma ShuffleIndex.insertVertical_zero_left {p n : ℕ} (s : ShuffleIndex p n)
    (x : Fin (n + 1)) :
    ((s.insertVertical 0).left.toOrderHom x.succ : ℕ) = (s.left.toOrderHom x : ℕ) := by
  rw [ShuffleIndex.left_apply, ShuffleIndex.left_apply]
  exact shuffleInsertion_zero_prefix_card s.val x

/-- 概要：先頭の水平挿入は最初の面に沿って第二座標を保つ。
方針：座標和と第一座標の増加を比較する。
規約：KST A.5。使われ方：第一因子の零番目の面の第二成分。 -/
lemma ShuffleIndex.insertHorizontal_zero_right {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (x : Fin (n + 1)) :
    (((s.insertHorizontal 0).right (show (p + 1) + q = n + 1 by omega)).toOrderHom x.succ : ℕ) =
      ((s.right h).toOrderHom x : ℕ) := by
  have h₁ := (s.insertHorizontal 0).coordinates_add (show (p + 1) + q = n + 1 by omega) x.succ
  have h₂ := s.coordinates_add h x
  have h₃ := s.insertHorizontal_zero_left x
  have hx : (x.succ : ℕ) = (x : ℕ) + 1 := rfl
  omega

/-- 概要：先頭の垂直挿入は最初の面に沿って第二座標を常に一つ増やす。
方針：座標和と第一座標の不変性を比較する。
規約：KST A.5。使われ方：第二因子の零番目の面。 -/
lemma ShuffleIndex.insertVertical_zero_right {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (x : Fin (n + 1)) :
    (((s.insertVertical 0).right (show p + (q + 1) = n + 1 by omega)).toOrderHom x.succ : ℕ) =
      ((s.right h).toOrderHom x : ℕ) + 1 := by
  have h₁ := (s.insertVertical 0).coordinates_add (show p + (q + 1) = n + 1 by omega) x.succ
  have h₂ := s.coordinates_add h x
  have h₃ := s.insertVertical_zero_left x
  have hx : (x.succ : ℕ) = (x : ℕ) + 1 := rfl
  omega

/-- 概要：先頭水平挿入の最初の面は第一因子の最初の面。
方針：各頂点の第一座標を比較する。
規約：KST A.5。使われ方：水平境界の先頭の項。 -/
lemma ShuffleIndex.insertHorizontal_first_left_face {p n : ℕ} (s : ShuffleIndex p n) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ (s.insertHorizontal 0).left =
      s.left ≫ SimplexCategory.δ (0 : Fin (p + 2)) := by
  ext x
  exact s.insertHorizontal_zero_left x

/-- 概要：先頭水平挿入の最初の面の第二写像は元のまま。
方針：各頂点の第二座標を比較する。
規約：KST A.5。使われ方：水平境界の先頭の項の第二成分。 -/
lemma ShuffleIndex.insertHorizontal_first_right_face {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫
        (s.insertHorizontal 0).right (show (p + 1) + q = n + 1 by omega) = s.right h := by
  ext x
  exact s.insertHorizontal_zero_right h x

/-- 概要：先頭垂直挿入の最初の面の第一写像は元のまま。
方針：各頂点の第一座標を比較する。
規約：KST A.5。使われ方：垂直境界の先頭の項の第一成分。 -/
lemma ShuffleIndex.insertVertical_first_left_face {p n : ℕ} (s : ShuffleIndex p n) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ (s.insertVertical 0).left = s.left := by
  ext x
  exact s.insertVertical_zero_left x

/-- 概要：先頭垂直挿入の最初の面は第二因子の最初の面。
方針：各頂点の第二座標を比較する。
規約：KST A.5。使われ方：垂直境界の先頭の項。 -/
lemma ShuffleIndex.insertVertical_first_right_face {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫
        (s.insertVertical 0).right (show p + (q + 1) = n + 1 by omega) =
      s.right h ≫ SimplexCategory.δ (0 : Fin (q + 2)) := by
  ext x
  exact s.insertVertical_zero_right h x

/-- 概要：末尾水平挿入の最後の面は第一因子の最後の面。
方針：挿入点より後の旧頂点はないため第一座標は保たれる。
規約：KST A.5。使われ方：水平境界の末尾の項。 -/
lemma ShuffleIndex.insertHorizontal_last_left_face {p n : ℕ} (s : ShuffleIndex p n) :
    SimplexCategory.δ (Fin.last (n + 1)) ≫ (s.insertHorizontal (Fin.last n)).left =
      s.left ≫ SimplexCategory.δ (Fin.last (p + 1)) := by
  ext x
  change ((s.insertHorizontal (Fin.last n)).left.toOrderHom ((Fin.last n).succ.succAbove x) : ℕ) =
    ((SimplexCategory.δ (Fin.last (p + 1))).toOrderHom (s.left.toOrderHom x) : ℕ)
  have hL : (s.left.toOrderHom x : ℕ) < p + 1 := (s.left.toOrderHom x).isLt
  rw [awFace_apply, Fin.val_last, ite_eq_left hL]
  have hx : ¬ n < (x : ℕ) := by have hx' : (x : ℕ) < n + 1 := x.isLt; omega
  simpa only [Fin.val_last, ite_eq_right hx, add_zero] using s.insertHorizontal_left (Fin.last n) x

/-- 概要：末尾水平挿入の最後の面の第二写像は元のまま。
方針：一般の水平挿入の第二座標の公式を使う。
規約：KST A.5。使われ方：水平境界の末尾の項の第二成分。 -/
lemma ShuffleIndex.insertHorizontal_last_right_face {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) :
    SimplexCategory.δ (Fin.last (n + 1)) ≫
        (s.insertHorizontal (Fin.last n)).right (show (p + 1) + q = n + 1 by omega) = s.right h := by
  ext x
  exact s.insertHorizontal_right h (Fin.last n) x

/-- 概要：末尾垂直挿入の最後の面の第一写像は元のまま。
方針：一般の垂直挿入の第一座標の公式を使う。
規約：KST A.5。使われ方：垂直境界の末尾の項の第一成分。 -/
lemma ShuffleIndex.insertVertical_last_left_face {p n : ℕ} (s : ShuffleIndex p n) :
    SimplexCategory.δ (Fin.last (n + 1)) ≫ (s.insertVertical (Fin.last n)).left = s.left := by
  ext x
  exact s.insertVertical_left (Fin.last n) x

/-- 概要：末尾垂直挿入の最後の面は第二因子の最後の面。
方針：挿入点より後の旧頂点はないため第二座標は保たれる。
規約：KST A.5。使われ方：垂直境界の末尾の項。 -/
lemma ShuffleIndex.insertVertical_last_right_face {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) :
    SimplexCategory.δ (Fin.last (n + 1)) ≫
        (s.insertVertical (Fin.last n)).right (show p + (q + 1) = n + 1 by omega) =
      s.right h ≫ SimplexCategory.δ (Fin.last (q + 1)) := by
  ext x
  change (((s.insertVertical (Fin.last n)).right (show p + (q + 1) = n + 1 by omega)).toOrderHom
      ((Fin.last n).succ.succAbove x) : ℕ) =
    ((SimplexCategory.δ (Fin.last (q + 1))).toOrderHom ((s.right h).toOrderHom x) : ℕ)
  have hR : ((s.right h).toOrderHom x : ℕ) < q + 1 := ((s.right h).toOrderHom x).isLt
  rw [awFace_apply, Fin.val_last, ite_eq_left hR]
  have hx : ¬ n < (x : ℕ) := by have hx' : (x : ℕ) < n + 1 := x.isLt; omega
  simpa only [Fin.val_last, ite_eq_right hx, add_zero] using s.insertVertical_right h (Fin.last n) x

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
