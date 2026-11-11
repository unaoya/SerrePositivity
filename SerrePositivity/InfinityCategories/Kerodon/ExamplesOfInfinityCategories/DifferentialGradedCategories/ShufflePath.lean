module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex
public import Mathlib.Order.Interval.Finset.Fin

/-!
# shuffle の二つの単体写像の格子路の性質

概要：水平・垂直ステップ数の和が頂点番号になり、両写像が格子路の両端を保つことを示す。
方針：各頂点以前のステップを部分集合と補集合に分ける。
規約：KST Construction A.5 の標準 shuffle。
使われ方：shuffle の面と退化の計算および AW との比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped Simplicial

/-- 概要：頂点 x より前の全ステップの数は x。
方針：Fin n の初区間、または全区間の濃度を計算する。
規約：KST A.5、x は最終頂点 n でもよい。
使われ方：二つの shuffle 座標の和。 -/
lemma shufflePrefix_card (n : ℕ) (x : Fin (n + 1)) :
    (Finset.univ.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))).card = x := by
  by_cases hx : (x : ℕ) < n
  · let y : Fin n := ⟨x, hx⟩
    have he : Finset.univ.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ)) = Finset.Iio y := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      rfl
    rw [he, Fin.card_Iio]
  · have hx' : (x : ℕ) = n := by have := x.isLt; omega
    have he : Finset.univ.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ)) = Finset.univ := by
      ext j
      simp [hx']
    rw [he, Finset.card_univ, Fintype.card_fin, hx']

/-- 概要：水平・垂直の前半ステップ数の和は全ステップ数。
方針：互いに素な二つの部分集合の合併の濃度を計算する。
規約：KST A.5、任意のステップ選択に成立。
使われ方：shuffle の第一・第二写像が同じ格子路を表すことの確認。 -/
lemma shufflePrefix_partition (n : ℕ) (s : Finset (Fin n)) (x : Fin (n + 1)) :
    (s.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))).card +
      (sᶜ.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))).card = x := by
  let A := s.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))
  let B := sᶜ.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have hs := (Finset.mem_filter.mp hj).1
    have ht := (Finset.mem_filter.mp hk).1
    exact (Finset.mem_compl.mp ht) hs
  have he : A ∪ B = Finset.univ.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ)) := by
    ext j
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_compl,
      Finset.mem_univ, true_and]
    tauto
  have hc := Finset.card_union_of_disjoint hd
  rw [he, shufflePrefix_card] at hc
  exact hc.symm

/-- 概要：shuffle の二つの座標の和は頂点番号。
方針：二つの座標を前半ステップ数の分割に戻す。
規約：KST A.5、第一因子の次数 p と第二因子の次数 q。
使われ方：面の削除時の格子路の分類。 -/
lemma ShuffleIndex.coordinates_add {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (x : Fin (n + 1)) :
    (s.left.toOrderHom x : ℕ) + ((s.right h).toOrderHom x : ℕ) = x := by
  rw [s.left_apply, s.right_apply]
  exact shufflePrefix_partition n s.val x

/-- 概要：shuffle の第一座標は最初の頂点で零。
方針：零番目の頂点以前のステップはない。
規約：KST A.5。使われ方：格子路の始点。 -/
@[simp] lemma ShuffleIndex.left_zero {p n : ℕ} (s : ShuffleIndex p n) :
    (s.left.toOrderHom 0 : ℕ) = 0 := by
  simp [s.left_apply]

/-- 概要：shuffle の第二座標は最初の頂点で零。
方針：零番目の頂点以前のステップはない。
規約：KST A.5。使われ方：格子路の始点。 -/
@[simp] lemma ShuffleIndex.right_zero {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n) :
    ((s.right h).toOrderHom 0 : ℕ) = 0 := by
  simp [s.right_apply]

/-- 概要：shuffle の第一座標の終点は p。
方針：最終頂点以前には全ての水平ステップがある。
規約：KST A.5。使われ方：格子路の終点。 -/
@[simp] lemma ShuffleIndex.left_last {p n : ℕ} (s : ShuffleIndex p n) :
    (s.left.toOrderHom (Fin.last n) : ℕ) = p := by
  rw [s.left_apply]
  have he : s.val.filter (fun j : Fin n ↦ (j : ℕ) < (Fin.last n : ℕ)) = s.val := by
    ext j
    simp
  rw [he, s.property]

/-- 概要：shuffle の第二座標の終点は q。
方針：最終頂点以前には全ての垂直ステップがある。
規約：KST A.5。使われ方：格子路の終点。 -/
@[simp] lemma ShuffleIndex.right_last {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n) :
    ((s.right h).toOrderHom (Fin.last n) : ℕ) = q := by
  rw [s.right_apply]
  have he : s.valᶜ.filter (fun j : Fin n ↦ (j : ℕ) < (Fin.last n : ℕ)) = s.valᶜ := by
    ext j
    simp
  rw [he, s.compl_card h]

/-- 概要：前半ステップ数は一歩で選択されたステップの分だけ増える。
方針：前半集合へ新しいステップ x を挿入するか、集合を保つ。
規約：KST A.5、任意のステップ選択。
使われ方：shuffle の水平・垂直ステップの分類。 -/
lemma shufflePrefix_succ {n : ℕ} (s : Finset (Fin n)) (x : Fin n) :
    (s.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ) + 1)).card =
      (s.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))).card + if x ∈ s then 1 else 0 := by
  by_cases hx : x ∈ s
  · have he : s.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ) + 1) =
        insert x (s.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))) := by
      ext j
      by_cases hj : j = x
      · subst j
        simp [hx]
      · have hv : (j : ℕ) ≠ (x : ℕ) := fun h ↦ hj (Fin.ext h)
        simp only [Finset.mem_filter, Finset.mem_insert, hj, false_or]
        exact and_congr_right (fun _ ↦ by omega)
    rw [he, Finset.card_insert_of_notMem (by simp)]
    simp [hx]
  · have he : s.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ) + 1) =
        s.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ)) := by
      ext j
      by_cases hj : j = x
      · subst j
        simp [hx]
      · have hv : (j : ℕ) ≠ (x : ℕ) := fun h ↦ hj (Fin.ext h)
        simp only [Finset.mem_filter]
        exact and_congr_right (fun _ ↦ by omega)
    rw [he]
    simp [hx]

/-- 概要：shuffle の第一座標は水平ステップでのみ一つ増える。
方針：前半集合への一つのステップの挿入を評価する。
規約：KST A.5。使われ方：面を削除したときの格子路の挙動。 -/
lemma ShuffleIndex.left_step {p n : ℕ} (s : ShuffleIndex p n) (x : Fin n) :
    (s.left.toOrderHom x.succ : ℕ) = (s.left.toOrderHom x.castSucc : ℕ) +
      if x ∈ s.val then 1 else 0 := by
  rw [s.left_apply, s.left_apply]
  exact shufflePrefix_succ s.val x

/-- 概要：shuffle の第二座標は垂直ステップでのみ一つ増える。
方針：補集合の前半への一つのステップの挿入を評価する。
規約：KST A.5。使われ方：水平・垂直の混合面の分類。 -/
lemma ShuffleIndex.right_step {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n) (x : Fin n) :
    ((s.right h).toOrderHom x.succ : ℕ) = ((s.right h).toOrderHom x.castSucc : ℕ) +
      if x ∉ s.val then 1 else 0 := by
  rw [s.right_apply, s.right_apply]
  simpa only [Finset.mem_compl, Fin.val_succ, Fin.val_castSucc] using shufflePrefix_succ s.valᶜ x

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

