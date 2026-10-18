module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCastCoordinates
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalDeletion
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalFace
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapFaces

/-!
# 連続する水平辺の境界面

概要：Berger–Fresse §1.1.3 の水平な同方向の境界面を一つ小さい shuffle と比較する。
方針：水平辺を削除し、辺数の移送を接頭辺数の計算と結びつける。
規約：大きい経路の辺数 p+1+q と小さい経路の頂点数 p+q+1 を明示して同定する。
使われ方：shuffle の Leibniz 則の第一の入力の微分に対応する面を求める。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：水平辺の削除後の水平座標は通過後に一つ小さくなる（Berger–Fresse §1.1.3）。
方針：辺集合を標準の長さへ移送して、属する辺の削除の接頭辺数の公式を使う。
規約：k は大きい経路の辺数と同じ長さの有限順序に属する。
使われ方：第一の入力で欠落する頂点を求める。 -/
lemma horizontalDeletion_horizontal_val {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a : Fin (p + 1 + q)) (ha : a ∈ s.val) (k : Fin (p + 1 + q)) :
    (s.horizontal (a.succ.succAbove k)).val =
      (((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).horizontal
        (Fin.cast (by omega : p + 1 + q = p + q + 1) k)).val +
          if a.val < k.val then 1 else 0 := by
  let e : Fin (p + 1 + q) ≃ Fin (p + q + 1) := finCongr (by omega)
  let S := s.val.map e.toEmbedding
  have haS : e a ∈ S := (Finset.mem_map' e.toEmbedding).2 ha
  have hcut : ((e a).succ.succAbove (e k)).val = (a.succ.succAbove k).val :=
    succAbove_succ_val_congr (e a) (e k) a k rfl rfl
  have h := erasePosition_filter_card_of_mem S (e a) haS (e k)
  rw [hcut] at h
  have hc := card_filter_finCongr (by omega : p + 1 + q = p + q + 1) s.val
    (a.succ.succAbove k).val
  change (S.filter (fun x => x.val < (a.succ.succAbove k).val)).card = _ at hc
  rw [hc] at h
  exact h

/-- 概要：水平辺を削除しても対応する面の垂直座標は変わらない（Berger–Fresse §1.1.3）。
方針：辺数の移送と補集合の可換性、および属さない辺の削除の公式を使う。
規約：垂直座標は水平辺集合の補集合の接頭辺数である。
使われ方：水平な同方向の面で第二の入力の頂点を保つ。 -/
lemma horizontalDeletion_vertical {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a : Fin (p + 1 + q)) (ha : a ∈ s.val) (k : Fin (p + 1 + q)) :
    s.vertical (a.succ.succAbove k) =
      ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).vertical
        (Fin.cast (by omega : p + 1 + q = p + q + 1) k) := by
  let e : Fin (p + 1 + q) ≃ Fin (p + q + 1) := finCongr (by omega)
  let S := s.val.map e.toEmbedding
  have haS : e a ∉ Sᶜ := by
    have hmem : e a ∈ S := (Finset.mem_map' e.toEmbedding).2 ha
    exact fun h => (Finset.mem_compl.mp h) hmem
  have hcut : ((e a).succ.succAbove (e k)).val = (a.succ.succAbove k).val :=
    succAbove_succ_val_congr (e a) (e k) a k rfl rfl
  have h := erasePosition_filter_card_of_notMem Sᶜ (e a) haS (e k)
  rw [erasePosition_compl, hcut] at h
  have hS : Sᶜ = s.valᶜ.map e.toEmbedding := map_finCongr_compl _ _
  rw [hS, card_filter_finCongr] at h
  apply Fin.ext
  exact h

/-- 概要：連続する水平辺の間の頂点の削除は第一の入力の一頂点の削除に対応する（Berger–Fresse §1.1.3）。
方針：接頭辺数の増分と単調性で、削除後の水平座標が欠落値の前後のどちらにあるか判定する。
規約：欠落値は元の水平座標 s.horizontal a.succ。
使われ方：水平な同方向の shuffle 面を第一の入力の面と比較する。 -/
lemma horizontalDeletion_horizontal {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a b : Fin (p + 1 + q)) (hab : b.val = a.val + 1)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (k : Fin (p + 1 + q)) :
    s.horizontal (a.succ.succAbove k) =
      (s.horizontal a.succ).succAbove
        (((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).horizontal
          (Fin.cast (by omega : p + 1 + q = p + q + 1) k)) := by
  let t := (horizontalInsertionEquiv p q a).symm ⟨s, ha⟩
  let l := Fin.cast (by omega : p + 1 + q = p + q + 1) k
  let j := s.horizontal a.succ
  have h₀ := (s.step_of_mem a ha).1
  have h₁ := (s.step_of_mem b hb).1
  have hba : b.castSucc = a.succ := Fin.ext hab
  rw [hba] at h₁
  have hv := horizontalDeletion_horizontal_val s a ha k
  change (s.horizontal (a.succ.succAbove k)).val = (t.horizontal l).val +
    if a.val < k.val then 1 else 0 at hv
  apply Fin.ext
  by_cases hk : a.val < k.val
  · have hcut : (a.succ.succAbove k).val = k.val + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ (by change a.val + 1 ≤ k.val; omega)]
      rfl
    have hm := s.horizontal.monotone (show b.succ ≤ a.succ.succAbove k from by
      change b.val + 1 ≤ (a.succ.succAbove k).val
      omega)
    rw [ite_eq_left hk] at hv
    have hj : j ≤ (t.horizontal l).castSucc := by
      change j.val ≤ (t.horizontal l).val
      change (s.horizontal b.succ).val ≤ (s.horizontal (a.succ.succAbove k)).val at hm
      change (s.horizontal b.succ).val = j.val + 1 at h₁
      omega
    change (s.horizontal (a.succ.succAbove k)).val = (j.succAbove (t.horizontal l)).val
    rw [Fin.succAbove_of_le_castSucc _ _ hj]
    exact hv
  · have hcut : (a.succ.succAbove k).val = k.val := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by change k.val < a.val + 1; omega)]
      rfl
    have hm := s.horizontal.monotone (show a.succ.succAbove k ≤ a.castSucc from by
      change (a.succ.succAbove k).val ≤ a.val
      omega)
    rw [ite_eq_right hk] at hv
    have hj : (t.horizontal l).castSucc < j := by
      change (t.horizontal l).val < j.val
      change (s.horizontal (a.succ.succAbove k)).val ≤ (s.horizontal a.castSucc).val at hm
      change j.val = (s.horizontal a.castSucc).val + 1 at h₀
      omega
    change (s.horizontal (a.succ.succAbove k)).val = (j.succAbove (t.horizontal l)).val
    rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    exact hv

/-- 概要：水平辺の間の頂点を削除する面写像（Berger–Fresse §1.1.3）。
方針：小さい経路の頂点の次数を移送してから頂点 a+1 を飛ばす。
規約：向きは [p+q] → [p+1+q]。
使われ方：水平な同方向の面を元の単体の引き戻しとして表す。 -/
def horizontalFaceMap (p q : ℕ) (a : Fin (p + 1 + q)) : ⦋p + q⦌ ⟶ ⦋p + 1 + q⦌ :=
  SimplexCategory.mkHom {
    toFun k := a.succ.succAbove (Fin.cast (by omega : p + q + 1 = p + 1 + q) k)
    monotone' := fun _ _ h => (Fin.strictMono_succAbove a.succ).monotone h }

/-- 概要：水平な同方向の shuffle 面は第一の入力の面との小さい shuffle に等しい（Berger–Fresse §1.1.3）。
方針：各頂点で水平座標の欠落値の公式と垂直座標の保存を使う。
規約：境界符号と shuffle 符号を除いた単体そのものの等式。
使われ方：Leibniz 則の第一の入力の微分に対応する境界項を同定する。 -/
lemma shuffleSimplex_horizontal_face (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath (p + 1) q) (a b : Fin (p + 1 + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    (simplicial (m + n)).map (horizontalFaceMap p q a).op
        (shuffleSimplex m n i (p := p + 1) (q := q) s x y) =
      shuffleSimplex m n i (p := p) (q := q) ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩)
        ((simplicial (m + 1)).δ (s.horizontal a.succ) x) y := by
  apply (simplexEquiv (m + n) (p + q)).injective
  funext k
  simp only [simplexEquiv_map, simplexEquiv_shuffleSimplex, simplexEquiv_δ]
  let l := Fin.cast (by omega : p + q + 1 = p + 1 + q) k
  have hcast : Fin.cast (by omega : p + 1 + q = p + q + 1) l = k := Fin.ext rfl
  change permutationComposition m n i
      (simplexEquiv (m + 1) (p + 1) x (s.horizontal (a.succ.succAbove l)))
      (simplexEquiv n q y (s.vertical (a.succ.succAbove l))) = _
  rw [horizontalDeletion_horizontal s a b hab ha hb l,
    horizontalDeletion_vertical s a ha l, hcast]

end SerrePositivity.EInfinity.BarrattEccles
