module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleDeletionCoordinates
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleStepMembership
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleComponent

/-!
# 連続する垂直辺の境界面

概要：Berger–Fresse §1.1.3 の shuffle の垂直な同方向の境界面を小さい shuffle と比較する。
方針：一つの垂直辺を削除し、座標の増分と単調性から入力の欠落頂点を同定する。
規約：辺 a,b は b=a+1 を満たす二つの垂直辺で、間の頂点 a+1 を削除する。
使われ方：shuffle の Leibniz 則の第二の入力の微分を表す面の比較となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：辺集合の補集合と辺位置の削除は可換する（Berger–Fresse §1.1.3）。
方針：削除は succAbove の逆像なので所属の否定と可換する。
規約：補集合はそれぞれの全辺集合で取る。
使われ方：垂直座標を水平辺集合の補集合によって計算する。 -/
lemma erasePosition_compl {N : ℕ} (s : Finset (Fin (N + 1))) (a : Fin (N + 1)) :
    erasePosition sᶜ a = (erasePosition s a)ᶜ := by
  ext j
  simp only [mem_erasePosition, Finset.mem_compl]

/-- 概要：垂直辺を削除しても対応する面の水平座標は変わらない（Berger–Fresse §1.1.3）。
方針：削除する位置が水平辺集合に属さない場合の接頭辺数の公式を使う。
規約：削除した経路の頂点 k は元の頂点 a+1 を飛ばして移す。
使われ方：垂直な同方向の境界面で第一の入力の頂点を保つ。 -/
lemma verticalDeletion_horizontal {p q : ℕ} (s : ShufflePath p (q + 1))
    (a : Fin (p + (q + 1))) (ha : a ∉ s.val) (k : Fin (p + q + 1)) :
    s.horizontal (a.succ.succAbove k) =
      ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).horizontal k := by
  apply Fin.ext
  exact erasePosition_filter_card_of_notMem s.val a ha k

/-- 概要：垂直辺の削除後の垂直座標は通過後に一つ小さくなる（Berger–Fresse §1.1.3）。
方針：垂直辺集合に属する位置の削除の接頭辺数の公式を使う。
規約：この補題は追加の隣接垂直辺を要求しない。
使われ方：同方向の境界面で第二の入力の欠落頂点を求める。 -/
lemma verticalDeletion_vertical_val {p q : ℕ} (s : ShufflePath p (q + 1))
    (a : Fin (p + (q + 1))) (ha : a ∉ s.val) (k : Fin (p + q + 1)) :
    (s.vertical (a.succ.succAbove k)).val =
      (((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).vertical k).val +
        if a.val < k.val then 1 else 0 := by
  have h := erasePosition_filter_card_of_mem s.valᶜ a (Finset.mem_compl.mpr ha) k
  rw [erasePosition_compl] at h
  exact h

/-- 概要：連続する垂直辺の間の頂点の削除は第二の入力の一頂点の削除に対応する（Berger–Fresse §1.1.3）。
方針：削除前後の座標の公式と隣接する二辺の増分から、欠落値の前後を単調性で判定する。
規約：欠落値は元の垂直座標 s.vertical a.succ である。
使われ方：垂直な同方向の shuffle 面を第二の入力の面と比較する。 -/
lemma verticalDeletion_vertical {p q : ℕ} (s : ShufflePath p (q + 1))
    (a b : Fin (p + (q + 1))) (hab : b.val = a.val + 1)
    (ha : a ∉ s.val) (hb : b ∉ s.val) (k : Fin (p + q + 1)) :
    s.vertical (a.succ.succAbove k) =
      (s.vertical a.succ).succAbove
        (((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).vertical k) := by
  let t := (verticalInsertionEquiv p q a).symm ⟨s, ha⟩
  let j := s.vertical a.succ
  have h₀ := (s.step_of_notMem a ha).2
  have h₁ := (s.step_of_notMem b hb).2
  have hba : b.castSucc = a.succ := Fin.ext hab
  rw [hba] at h₁
  have hv := verticalDeletion_vertical_val s a ha k
  change (s.vertical (a.succ.succAbove k)).val = (t.vertical k).val +
    if a.val < k.val then 1 else 0 at hv
  apply Fin.ext
  by_cases hk : a.val < k.val
  · have hcut : (a.succ.succAbove k).val = k.val + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ (by change a.val + 1 ≤ k.val; omega)]
      rfl
    have hm := s.vertical.monotone (show b.succ ≤ a.succ.succAbove k from by
      change b.val + 1 ≤ (a.succ.succAbove k).val
      omega)
    rw [ite_eq_left hk] at hv
    have hj : j ≤ (t.vertical k).castSucc := by
      change j.val ≤ (t.vertical k).val
      change (s.vertical b.succ).val ≤ (s.vertical (a.succ.succAbove k)).val at hm
      change (s.vertical b.succ).val = j.val + 1 at h₁
      omega
    change (s.vertical (a.succ.succAbove k)).val = (j.succAbove (t.vertical k)).val
    rw [Fin.succAbove_of_le_castSucc _ _ hj]
    exact hv
  · have hcut : (a.succ.succAbove k).val = k.val := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by change k.val < a.val + 1; omega)]
      rfl
    have hm := s.vertical.monotone (show a.succ.succAbove k ≤ a.castSucc from by
      change (a.succ.succAbove k).val ≤ a.val
      omega)
    rw [ite_eq_right hk] at hv
    have hj : (t.vertical k).castSucc < j := by
      change (t.vertical k).val < j.val
      change (s.vertical (a.succ.succAbove k)).val ≤ (s.vertical a.castSucc).val at hm
      change j.val = (s.vertical a.castSucc).val + 1 at h₀
      omega
    change (s.vertical (a.succ.succAbove k)).val = (j.succAbove (t.vertical k)).val
    rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    exact hv

/-- 概要：連続する垂直辺の間の shuffle 面は第二の入力の面との小さい shuffle に等しい（Berger–Fresse §1.1.3）。
方針：置換列の各頂点で水平座標の保存と垂直座標の欠落値の公式を適用する。
規約：面の符号と shuffle 符号はまだこの等式に含めない。
使われ方：Leibniz 則の第二の入力の微分に対応する境界項を同定する。 -/
lemma shuffleSimplex_vertical_face (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath p (q + 1)) (a b : Fin (p + (q + 1)))
    (hab : b.val = a.val + 1) (ha : a ∉ s.val) (hb : b ∉ s.val)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (simplicial (m + n)).δ a.succ (shuffleSimplex m n i (p := p) (q := q + 1) s x y) =
      shuffleSimplex m n i (p := p) (q := q) ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩) x
        ((simplicial n).δ (s.vertical a.succ) y) := by
  apply (simplexEquiv (m + n) (p + q)).injective
  funext k
  erw [simplexEquiv_δ (m + n) (p + q),
    simplexEquiv_shuffleSimplex m n i (p := p) (q := q + 1)]
  simp only [simplexEquiv_δ, simplexEquiv_shuffleSimplex]
  rw [verticalDeletion_horizontal s a ha k, verticalDeletion_vertical s a b hab ha hb k]

end SerrePositivity.EInfinity.BarrattEccles
