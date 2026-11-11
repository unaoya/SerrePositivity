module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleInsert
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleSwapSign

/-!
# 一ステップ挿入による shuffle の逆転数

概要：挿入したステップの前後の水平・垂直ステップ数から逆転数の増分を計算する。
方針：逆転数を水平ステップ直前の垂直座標の和とし、新旧の集合の像を比較する。
規約：KST Construction A.5 の標準 shuffle。
使われ方：同種ステップの面の符号と各因子の交代境界の符号を同定する。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：水平挿入後の垂直集合は元の垂直集合を標準包含で移した集合。
方針：包含関係と補集合の濃度の一致を使う。
規約：KST A.5。使われ方：水平挿入後の垂直座標の比較。 -/
lemma ShuffleIndex.insertHorizontal_compl {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin (n + 1)) :
    (s.insertHorizontal a).valᶜ = s.valᶜ.map a.succAboveEmb := by
  have hsub : s.valᶜ.map a.succAboveEmb ⊆ (s.insertHorizontal a).valᶜ := by
    intro z hz
    rcases Finset.mem_map.mp hz with ⟨j, hj, rfl⟩
    rw [Finset.mem_compl]
    change a.succAbove j ∉ (s.insertHorizontal a).val
    rw [s.insertHorizontal_mem_image]
    exact Finset.mem_compl.mp hj
  have hc : (s.insertHorizontal a).valᶜ.card = (s.valᶜ.map a.succAboveEmb).card := by
    rw [Finset.card_compl, (s.insertHorizontal a).property, Finset.card_map,
      Finset.card_compl, s.property]
    simp
  exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq hc)).symm

/-- 概要：水平挿入は既存の各水平ステップ直前の垂直座標を保つ。
方針：垂直集合の像と順序を保つ標準包含の前半の濃度を比較する。
規約：KST A.5。使われ方：元の水平ステップの逆転数への寄与の不変性。 -/
lemma ShuffleIndex.insertHorizontal_right_image {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin (n + 1)) (x : Fin n) :
    (((s.insertHorizontal a).right (show (p + 1) + q = n + 1 by omega)).toOrderHom
      (a.succAbove x).castSucc : ℕ) = ((s.right h).toOrderHom x.castSucc : ℕ) := by
  rw [ShuffleIndex.right_apply, ShuffleIndex.right_apply, s.insertHorizontal_compl,
    Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro j _
  change a.succAbove j < a.succAbove x ↔ j < x
  exact (Fin.succAboveOrderEmb a).lt_iff_lt

/-- 概要：挿入した水平ステップ直前の垂直座標は、元の挿入位置の垂直座標。
方針：挿入を飛ばす頂点の公式を挿入位置自身へ適用する。
規約：KST A.5。使われ方：新しい水平ステップの逆転数への寄与。 -/
lemma ShuffleIndex.insertHorizontal_right_insert {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin (n + 1)) :
    (((s.insertHorizontal a).right (show (p + 1) + q = n + 1 by omega)).toOrderHom a.castSucc : ℕ) =
      ((s.right h).toOrderHom a : ℕ) := by
  have ht := s.insertHorizontal_right h a a
  simpa only [Fin.succAbove_succ_self] using ht

/-- 概要：水平挿入は元の位置以前の垂直ステップ数だけ逆転数を増やす。
方針：既存の水平ステップの寄与は変わらず、新しい水平ステップの寄与を足す。
規約：KST A.5、先頭・末尾の挿入も含む。
使われ方：水平の通常境界の交代符号との比較。 -/
lemma ShuffleIndex.insertHorizontal_inversions {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin (n + 1)) :
    (s.insertHorizontal a).inversions = s.inversions + ((s.right h).toOrderHom a : ℕ) := by
  rw [(s.insertHorizontal a).inversions_eq_right (show (p + 1) + q = n + 1 by omega)]
  change (∑ j ∈ insert a (s.val.map a.succAboveEmb),
    (((s.insertHorizontal a).right (show (p + 1) + q = n + 1 by omega)).toOrderHom j.castSucc : ℕ)) = _
  rw [Finset.sum_insert (shuffleInsertion_not_mem s.val a), Finset.sum_map,
    s.insertHorizontal_right_insert h a]
  have he : (∑ j ∈ s.val,
      (((s.insertHorizontal a).right (show (p + 1) + q = n + 1 by omega)).toOrderHom
        (a.succAboveEmb j).castSucc : ℕ)) = s.inversions := by
    rw [s.inversions_eq_right h]
    apply Finset.sum_congr rfl
    intro j _
    exact s.insertHorizontal_right_image h a j
  rw [he, Nat.add_comm]

/-- 概要：水平挿入の内部の面の符号は第一因子の面の符号に一致。
方針：挿入による逆転数の増分と二つの座標の和を使い、偶数の垂直数を取り除く。
規約：KST A.5、間の頂点 a+1 を削除する面。
使われ方：水平の境界項の交代符号の照合。 -/
lemma ShuffleIndex.insertHorizontal_face_sign {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin (n + 1)) :
    (-1 : ℤ) ^ ((a : ℕ) + 1) * (-1 : ℤ) ^ (s.insertHorizontal a).inversions =
      (-1 : ℤ) ^ ((s.left.toOrderHom a : ℕ) + 1) * (-1 : ℤ) ^ s.inversions := by
  rw [s.insertHorizontal_inversions h a, ← pow_add, ← pow_add]
  have ht := s.coordinates_add h a
  have he : (a : ℕ) + 1 + (s.inversions + ((s.right h).toOrderHom a : ℕ)) =
      ((s.left.toOrderHom a : ℕ) + 1 + s.inversions) + 2 * ((s.right h).toOrderHom a : ℕ) := by omega
  rw [he, pow_add, pow_mul]
  simp

/-- 概要：標準包含で移した旧ステップの番号は挿入点以後で一つ増える。
方針：Fin.succAbove の二つの分岐を評価する。
規約：KST A.5。使われ方：垂直挿入後の旧水平ステップ直前の座標。 -/
lemma shuffleInsertion_step_val {n : ℕ} (a : Fin (n + 1)) (j : Fin n) :
    (a.succAbove j : ℕ) = (j : ℕ) + if (a : ℕ) ≤ (j : ℕ) then 1 else 0 := by
  simp only [Fin.succAbove]
  split_ifs <;> simp_all only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] <;> omega

/-- 概要：垂直挿入は旧ステップ直前の第一座標を保つ。
方針：水平集合を順序を保つ単射で移し、前半の濃度を比較する。
規約：KST A.5。使われ方：旧水平ステップの逆転数への寄与。 -/
lemma ShuffleIndex.insertVertical_left_image {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin (n + 1)) (x : Fin n) :
    ((s.insertVertical a).left.toOrderHom (a.succAbove x).castSucc : ℕ) =
      (s.left.toOrderHom x.castSucc : ℕ) := by
  rw [ShuffleIndex.left_apply, ShuffleIndex.left_apply]
  change ((s.val.map a.succAboveEmb).filter
    (fun j : Fin (n + 1) ↦ (j : ℕ) < (a.succAbove x : ℕ))).card = _
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro j _
  change a.succAbove j < a.succAbove x ↔ j < x
  exact (Fin.succAboveOrderEmb a).lt_iff_lt

/-- 概要：垂直挿入は旧ステップ直前の第二座標を挿入位置以後で一つ増やす。
方針：旧ステップの番号の増分と第一座標の不変性を座標和に代入する。
規約：KST A.5。使われ方：垂直挿入の逆転数の増分。 -/
lemma ShuffleIndex.insertVertical_right_image {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin (n + 1)) (x : Fin n) :
    (((s.insertVertical a).right (show p + (q + 1) = n + 1 by omega)).toOrderHom
      (a.succAbove x).castSucc : ℕ) = ((s.right h).toOrderHom x.castSucc : ℕ) +
        if (a : ℕ) ≤ (x : ℕ) then 1 else 0 := by
  have h₁ := (s.insertVertical a).coordinates_add (show p + (q + 1) = n + 1 by omega)
    (a.succAbove x).castSucc
  have h₂ := s.coordinates_add h x.castSucc
  have h₃ := s.insertVertical_left_image a x
  have h₄ := shuffleInsertion_step_val a x
  have hv : ((a.succAbove x).castSucc : Fin (n + 2)).val = (a.succAbove x : ℕ) := rfl
  have hx : (x.castSucc : Fin (n + 1)).val = (x : ℕ) := rfl
  omega

/-- 概要：挿入位置以後の水平ステップ数は p から第一座標を引いた数。
方針：水平集合を位置より前とそれ以後の二つの部分に分ける。
規約：KST A.5、挿入位置自身の旧ステップも後半に含める。
使われ方：垂直挿入で増える逆転の数。 -/
lemma ShuffleIndex.suffix_card {p n : ℕ} (s : ShuffleIndex p n) (a : Fin (n + 1)) :
    (s.val.filter (fun j : Fin n ↦ (a : ℕ) ≤ (j : ℕ))).card =
      p - (s.left.toOrderHom a : ℕ) := by
  have hc := Finset.card_filter_add_card_filter_not (s := s.val)
    (fun j : Fin n ↦ (j : ℕ) < (a : ℕ))
  simp only [not_lt, s.property] at hc
  have hp : (s.val.filter (fun j : Fin n ↦ (j : ℕ) < (a : ℕ))).card =
      (s.left.toOrderHom a : ℕ) := rfl
  omega

/-- 概要：垂直挿入は位置以後の水平ステップ数だけ逆転数を増やす。
方針：各旧水平ステップ直前の垂直座標の増分を足す。
規約：KST A.5、先頭・末尾の挿入も含む。
使われ方：垂直の通常境界の交代符号との比較。 -/
lemma ShuffleIndex.insertVertical_inversions {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin (n + 1)) :
    (s.insertVertical a).inversions = s.inversions + (p - (s.left.toOrderHom a : ℕ)) := by
  rw [(s.insertVertical a).inversions_eq_right (show p + (q + 1) = n + 1 by omega)]
  change (∑ j ∈ s.val.map a.succAboveEmb,
    (((s.insertVertical a).right (show p + (q + 1) = n + 1 by omega)).toOrderHom j.castSucc : ℕ)) = _
  rw [Finset.sum_map]
  have he : (∑ j ∈ s.val,
      (((s.insertVertical a).right (show p + (q + 1) = n + 1 by omega)).toOrderHom
        (a.succAboveEmb j).castSucc : ℕ)) =
      ∑ j ∈ s.val, (((s.right h).toOrderHom j.castSucc : ℕ) +
        if (a : ℕ) ≤ (j : ℕ) then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    exact s.insertVertical_right_image h a j
  rw [he, Finset.sum_add_distrib, ← s.inversions_eq_right h]
  have hi : (∑ j ∈ s.val, if (a : ℕ) ≤ (j : ℕ) then 1 else 0) =
      (s.val.filter (fun j : Fin n ↦ (a : ℕ) ≤ (j : ℕ))).card := by
    rw [← Finset.sum_filter]
    simp
  rw [hi, s.suffix_card]

/-- 概要：垂直挿入の内部の面の符号は第二因子の面の全複体の符号に一致。
方針：挿入の逆転数の増分と座標和を使い、指数の整数の等式を示す。
規約：KST A.5、垂直微分の外側の符号は (−1)^p。
使われ方：垂直の境界項の交代符号の照合。 -/
lemma ShuffleIndex.insertVertical_face_sign {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin (n + 1)) :
    (-1 : ℤ) ^ ((a : ℕ) + 1) * (-1 : ℤ) ^ (s.insertVertical a).inversions =
      (-1 : ℤ) ^ p * ((-1 : ℤ) ^ (((s.right h).toOrderHom a : ℕ) + 1) *
        (-1 : ℤ) ^ s.inversions) := by
  rw [s.insertVertical_inversions h a, ← pow_add, ← pow_add, ← pow_add]
  have ht := s.coordinates_add h a
  have hL : (s.left.toOrderHom a : ℕ) ≤ p := Nat.le_of_lt_succ (s.left.toOrderHom a).isLt
  congr 1
  omega

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

