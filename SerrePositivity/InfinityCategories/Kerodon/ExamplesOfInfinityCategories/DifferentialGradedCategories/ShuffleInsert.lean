module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShufflePath

/-!
# shuffle への水平・垂直ステップの挿入

概要：一つのステップを挿入した二種類の shuffle と、その水平集合の所属を構成する。
方針：挿入点を飛ばす標準包含で既存ステップを移し、水平挿入の場合だけ挿入点を加える。
規約：KST Construction A.5 の標準 shuffle。
使われ方：同種ステップの内部の面と、端点の面を各因子の通常境界へ対応させる。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped Simplicial

/-- 概要：ステップ挿入の標準包含の像に挿入点は属さない。
方針：Fin.succAbove は指定された番号を飛ばす。
規約：KST A.5。使われ方：水平挿入後の濃度の計算。 -/
lemma shuffleInsertion_not_mem {n : ℕ} (s : Finset (Fin n)) (a : Fin (n + 1)) :
    a ∉ s.map a.succAboveEmb := by
  intro ha
  rcases Finset.mem_map.mp ha with ⟨x, _, hx⟩
  exact (Fin.succAbove_ne a x) hx

/-- 概要：指定位置に一つ水平ステップを挿入する。
方針：元の水平集合を標準包含で移し、新しい位置を加える。
規約：KST A.5、水平ステップ数 p が p+1 になる。
使われ方：第一因子の境界に対応する shuffle の構成。 -/
def ShuffleIndex.insertHorizontal {p n : ℕ} (s : ShuffleIndex p n) (a : Fin (n + 1)) :
    ShuffleIndex (p + 1) (n + 1) :=
  ⟨insert a (s.val.map a.succAboveEmb), by
    rw [Finset.card_insert_of_notMem (shuffleInsertion_not_mem s.val a),
      Finset.card_map, s.property]⟩

/-- 概要：指定位置に一つ垂直ステップを挿入する。
方針：水平集合を標準包含で移し、新しい位置を水平集合に加えない。
規約：KST A.5、水平ステップ数 p は保つ。
使われ方：第二因子の境界に対応する shuffle の構成。 -/
def ShuffleIndex.insertVertical {p n : ℕ} (s : ShuffleIndex p n) (a : Fin (n + 1)) :
    ShuffleIndex p (n + 1) :=
  ⟨s.val.map a.succAboveEmb, by rw [Finset.card_map, s.property]⟩

/-- 概要：水平挿入の位置は新しい水平集合に属する。
方針：挿入による所属を評価する。
規約：KST A.5。使われ方：挿入ステップの種類の確認。 -/
@[simp] lemma ShuffleIndex.insertHorizontal_mem {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin (n + 1)) : a ∈ (s.insertHorizontal a).val := Finset.mem_insert_self _ _

/-- 概要：垂直挿入の位置は新しい水平集合に属さない。
方針：標準包含が指定位置を飛ばすことを使う。
規約：KST A.5。使われ方：挿入ステップの種類の確認。 -/
@[simp] lemma ShuffleIndex.insertVertical_not_mem {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin (n + 1)) : a ∉ (s.insertVertical a).val := shuffleInsertion_not_mem s.val a

/-- 概要：水平挿入で元のステップの水平・垂直属性は保たれる。
方針：標準包含の単射性と、新しい位置の非所属を使う。
規約：KST A.5。使われ方：同種ステップの面の分類。 -/
@[simp] lemma ShuffleIndex.insertHorizontal_mem_image {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin (n + 1)) (j : Fin n) :
    a.succAbove j ∈ (s.insertHorizontal a).val ↔ j ∈ s.val := by
  change a.succAbove j ∈ insert a (s.val.map a.succAboveEmb) ↔ _
  rw [Finset.mem_insert]
  simp only [Fin.succAbove_ne, false_or]
  exact Finset.mem_map' a.succAboveEmb

/-- 概要：垂直挿入で元のステップの水平・垂直属性は保たれる。
方針：標準包含の単射性を使う。
規約：KST A.5。使われ方：同種ステップの面の分類。 -/
@[simp] lemma ShuffleIndex.insertVertical_mem_image {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin (n + 1)) (j : Fin n) :
    a.succAbove j ∈ (s.insertVertical a).val ↔ j ∈ s.val :=
  Finset.mem_map' a.succAboveEmb

/-- 概要：挿入を飛ばした頂点で、既存ステップの前後関係は保たれる。
方針：ステップと頂点の二つの標準包含の分岐を整数で比較する。
規約：KST A.5、頂点の包含は挿入ステップの直後の頂点を飛ばす。
使われ方：挿入前後の格子路座標の計算。 -/
lemma shuffleInsertion_prefix_compare {n : ℕ} (a : Fin (n + 1)) (j : Fin n)
    (x : Fin (n + 1)) :
    (a.succAbove j : ℕ) < (a.succ.succAbove x : ℕ) ↔ (j : ℕ) < (x : ℕ) := by
  simp only [Fin.succAbove]
  split_ifs <;> simp_all only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] <;> omega

/-- 概要：標準包含で移した水平集合の前半の濃度は元の前半の濃度に一致。
方針：フィルターと単射による像を交換し、前後関係の同値を使う。
規約：KST A.5。使われ方：水平・垂直挿入の座標の共通部分。 -/
lemma shuffleInsertion_prefix_card {n : ℕ} (s : Finset (Fin n)) (a : Fin (n + 1))
    (x : Fin (n + 1)) :
    ((s.map a.succAboveEmb).filter
      (fun j : Fin (n + 1) ↦ (j : ℕ) < (a.succ.succAbove x : ℕ))).card =
      (s.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))).card := by
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro j _
  exact shuffleInsertion_prefix_compare a j x

/-- 概要：挿入を飛ばした頂点は、挿入点の後でのみ番号が一つ増える。
方針：標準包含の二つの分岐を評価する。
規約：KST A.5。使われ方：挿入後の二つの格子路座標の和。 -/
lemma shuffleInsertion_vertex_val {n : ℕ} (a : Fin (n + 1)) (x : Fin (n + 1)) :
    (a.succ.succAbove x : ℕ) = (x : ℕ) + if (a : ℕ) < (x : ℕ) then 1 else 0 := by
  simp only [Fin.succAbove]
  split_ifs <;> simp_all only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] <;> omega

/-- 概要：挿入点は、対応する元の頂点が挿入点より後の場合にのみ前半に属する。
方針：挿入を飛ばす頂点包含の値を比較する。
規約：KST A.5。使われ方：水平挿入の前半ステップ数の増分。 -/
lemma shuffleInsertion_vertex_after {n : ℕ} (a : Fin (n + 1)) (x : Fin (n + 1)) :
    (a : ℕ) < (a.succ.succAbove x : ℕ) ↔ (a : ℕ) < (x : ℕ) := by
  rw [shuffleInsertion_vertex_val]
  split_ifs <;> omega

/-- 概要：垂直挿入は、挿入を飛ばした頂点で第一座標を保つ。
方針：移した水平集合の前半の濃度の不変性を使う。
規約：KST A.5。使われ方：垂直の同種ステップの面の比較。 -/
lemma ShuffleIndex.insertVertical_left {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin (n + 1)) (x : Fin (n + 1)) :
    ((s.insertVertical a).left.toOrderHom (a.succ.succAbove x) : ℕ) =
      (s.left.toOrderHom x : ℕ) := by
  rw [ShuffleIndex.left_apply, ShuffleIndex.left_apply]
  exact shuffleInsertion_prefix_card s.val a x

/-- 概要：水平挿入は、挿入を飛ばした頂点で第一座標を後半のみ一つ増やす。
方針：前半のフィルターに挿入点を加える場合の濃度を計算する。
規約：KST A.5。使われ方：水平の同種ステップの面の比較。 -/
lemma ShuffleIndex.insertHorizontal_left {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin (n + 1)) (x : Fin (n + 1)) :
    ((s.insertHorizontal a).left.toOrderHom (a.succ.succAbove x) : ℕ) =
      (s.left.toOrderHom x : ℕ) + if (a : ℕ) < (x : ℕ) then 1 else 0 := by
  rw [ShuffleIndex.left_apply, ShuffleIndex.left_apply]
  change ((insert a (s.val.map a.succAboveEmb)).filter
    (fun j : Fin (n + 1) ↦ (j : ℕ) < (a.succ.succAbove x : ℕ))).card = _
  rw [Finset.filter_insert]
  by_cases hx : (a : ℕ) < (x : ℕ)
  · have hp := (shuffleInsertion_vertex_after a x).mpr hx
    rw [ite_eq_left hp, Finset.card_insert_of_notMem (by
      intro ha
      exact shuffleInsertion_not_mem s.val a (Finset.mem_filter.mp ha).1),
      shuffleInsertion_prefix_card, ite_eq_left hx]
  · have hp : ¬ (a : ℕ) < (a.succ.succAbove x : ℕ) := by
      rw [shuffleInsertion_vertex_after]
      exact hx
    rw [ite_eq_right hp, shuffleInsertion_prefix_card, ite_eq_right hx, add_zero]

/-- 概要：水平挿入は、挿入を飛ばした頂点で第二座標を保つ。
方針：二つの座標の和と第一座標の増分を比較する。
規約：KST A.5、第二因子の次数は q のまま。
使われ方：第一因子の境界へ対応させる写像の第二成分。 -/
lemma ShuffleIndex.insertHorizontal_right {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin (n + 1)) (x : Fin (n + 1)) :
    (((s.insertHorizontal a).right (show (p + 1) + q = n + 1 by omega)).toOrderHom
      (a.succ.succAbove x) : ℕ) = ((s.right h).toOrderHom x : ℕ) := by
  have h₁ := (s.insertHorizontal a).coordinates_add (show (p + 1) + q = n + 1 by omega)
    (a.succ.succAbove x)
  have h₂ := s.coordinates_add h x
  have h₃ := s.insertHorizontal_left a x
  have h₄ := shuffleInsertion_vertex_val a x
  omega

/-- 概要：垂直挿入は、挿入を飛ばした頂点で第二座標を後半のみ一つ増やす。
方針：二つの座標の和と第一座標の不変性を比較する。
規約：KST A.5、第二因子の次数 q が q+1 になる。
使われ方：第二因子の境界へ対応させる写像の第二成分。 -/
lemma ShuffleIndex.insertVertical_right {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin (n + 1)) (x : Fin (n + 1)) :
    (((s.insertVertical a).right (show p + (q + 1) = n + 1 by omega)).toOrderHom
      (a.succ.succAbove x) : ℕ) = ((s.right h).toOrderHom x : ℕ) +
        if (a : ℕ) < (x : ℕ) then 1 else 0 := by
  have h₁ := (s.insertVertical a).coordinates_add (show p + (q + 1) = n + 1 by omega)
    (a.succ.succAbove x)
  have h₂ := s.coordinates_add h x
  have h₃ := s.insertVertical_left a x
  have h₄ := shuffleInsertion_vertex_val a x
  omega

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

