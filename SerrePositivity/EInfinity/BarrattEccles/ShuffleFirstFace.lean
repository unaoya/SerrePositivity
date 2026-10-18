module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLastFace
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleFirstPosition

/-!
# shuffle の始端の境界面

概要：Berger–Fresse §1.1.3 の shuffle の最初の面を、最初の辺の向きに応じて比較する。
方針：先頭の辺を削除した接頭辺数の公式から座標の保存と後続への移動を求める。
規約：水平始端は第一の入力の δ 0、垂直始端は第二の入力の δ 0 に対応する。
使われ方：shuffle の Leibniz 則の左端の境界項を同定する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：垂直始端を削除した面の水平座標は変わらない（Berger–Fresse §1.1.3）。
方針：先頭が水平辺集合に属さない場合の接頭辺数を計算する。
規約：元の頂点 k.succ と小さい経路の頂点 k を比較する。
使われ方：垂直始端の面で第一の入力の頂点を保存する。 -/
lemma verticalDeletion_first_horizontal {p q : ℕ} (s : ShufflePath p (q + 1))
    (h₀ : 0 ∉ s.val) (k : Fin (p + q + 1)) :
    s.horizontal k.succ = ((verticalInsertionEquiv p q 0).symm ⟨s, h₀⟩).horizontal k := by
  apply Fin.ext
  exact erase_first_filter_card_of_notMem s.val h₀ k.val

/-- 概要：垂直始端を削除した面の垂直座標は小さい経路の後続値である（Berger–Fresse §1.1.3）。
方針：垂直辺集合が先頭を含むことから接頭辺数の増分を求める。
規約：値を一つ増やす Fin.succ によって比較する。
使われ方：第二の入力の最初の頂点の削除を表す。 -/
lemma verticalDeletion_first_vertical {p q : ℕ} (s : ShufflePath p (q + 1))
    (h₀ : 0 ∉ s.val) (k : Fin (p + q + 1)) :
    s.vertical k.succ = (((verticalInsertionEquiv p q 0).symm ⟨s, h₀⟩).vertical k).succ := by
  have h := erase_first_filter_card_of_mem s.valᶜ (Finset.mem_compl.mpr h₀) k.val
  rw [erasePosition_compl] at h
  apply Fin.ext
  exact h

/-- 概要：水平始端を削除した面の水平座標は小さい経路の後続値である（Berger–Fresse §1.1.3）。
方針：辺数の移送後に先頭辺の接頭辺数の増分を計算する。
規約：次数の同定では頂点番号の値を変えない。
使われ方：第一の入力の最初の頂点の削除を表す。 -/
lemma horizontalDeletion_first_horizontal {p q : ℕ} (s : ShufflePath (p + 1) q)
    (h₀ : 0 ∈ s.val) (k : Fin (p + 1 + q)) :
    s.horizontal k.succ =
      (((horizontalInsertionEquiv p q 0).symm ⟨s, h₀⟩).horizontal
        (Fin.cast (by omega : p + 1 + q = p + q + 1) k)).succ := by
  let e : Fin (p + 1 + q) ≃ Fin (p + q + 1) := finCongr (by omega)
  let S := s.val.map e.toEmbedding
  have hS : (0 : Fin (p + q + 1)) ∈ S := (Finset.mem_map' e.toEmbedding).2 h₀
  have h := erase_first_filter_card_of_mem S hS k.val
  have hc := card_filter_finCongr (by omega : p + 1 + q = p + q + 1) s.val (k.val + 1)
  change (S.filter (fun x => x.val < k.val + 1)).card = _ at hc
  rw [hc] at h
  apply Fin.ext
  exact h

/-- 概要：水平始端を削除した面の垂直座標は変わらない（Berger–Fresse §1.1.3）。
方針：水平辺の補集合は先頭を含まないことと接頭辺数の保存を使う。
規約：小さい経路の頂点の次数は Fin.cast で同定する。
使われ方：水平始端の面で第二の入力の頂点を保存する。 -/
lemma horizontalDeletion_first_vertical {p q : ℕ} (s : ShufflePath (p + 1) q)
    (h₀ : 0 ∈ s.val) (k : Fin (p + 1 + q)) :
    s.vertical k.succ = ((horizontalInsertionEquiv p q 0).symm ⟨s, h₀⟩).vertical
      (Fin.cast (by omega : p + 1 + q = p + q + 1) k) := by
  let e : Fin (p + 1 + q) ≃ Fin (p + q + 1) := finCongr (by omega)
  let S := s.val.map e.toEmbedding
  have hS : (0 : Fin (p + q + 1)) ∉ Sᶜ := by
    have hmem : (0 : Fin (p + q + 1)) ∈ S := (Finset.mem_map' e.toEmbedding).2 h₀
    exact fun h => (Finset.mem_compl.mp h) hmem
  have h := erase_first_filter_card_of_notMem Sᶜ hS k.val
  rw [erasePosition_compl] at h
  have hSc : Sᶜ = s.valᶜ.map e.toEmbedding := map_finCongr_compl _ _
  rw [hSc, card_filter_finCongr] at h
  apply Fin.ext
  exact h

/-- 概要：水平始端の面を表す単体圏の射（Berger–Fresse §1.1.3）。
方針：小さい経路の頂点の次数を移して一つ後続へ送る。
規約：最初の頂点 0 を飛ばす面写像である。
使われ方：水平始端の shuffle 面の次数を明示する。 -/
def horizontalFirstFaceMap (p q : ℕ) : ⦋p + q⦌ ⟶ ⦋p + 1 + q⦌ :=
  SimplexCategory.mkHom {
    toFun k := (Fin.cast (by omega : p + q + 1 = p + 1 + q) k).succ
    monotone' := fun _ _ h => Fin.succ_le_succ_iff.mpr h }

/-- 概要：水平始端の shuffle 面は第一の入力の最初の面を用いる（Berger–Fresse §1.1.3）。
方針：第一の座標を後続へ送り、第二の座標を保存する公式を各頂点へ適用する。
規約：符号を除いた単体の等式である。
使われ方：第一の入力の最初の境界項を同定する。 -/
lemma shuffleSimplex_horizontal_first_face (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath (p + 1) q) (h₀ : 0 ∈ s.val)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    (simplicial (m + n)).map (horizontalFirstFaceMap p q).op
        (shuffleSimplex m n i (p := p + 1) (q := q) s x y) =
      shuffleSimplex m n i (p := p) (q := q) ((horizontalInsertionEquiv p q 0).symm ⟨s, h₀⟩)
        ((simplicial (m + 1)).δ 0 x) y := by
  apply (simplexEquiv (m + n) (p + q)).injective
  funext k
  simp only [simplexEquiv_map, simplexEquiv_shuffleSimplex, simplexEquiv_δ, Fin.succAbove_zero]
  let l := Fin.cast (by omega : p + q + 1 = p + 1 + q) k
  have hcast : Fin.cast (by omega : p + 1 + q = p + q + 1) l = k := Fin.ext rfl
  change permutationComposition m n i
      (simplexEquiv (m + 1) (p + 1) x (s.horizontal l.succ))
      (simplexEquiv n q y (s.vertical l.succ)) = _
  rw [horizontalDeletion_first_horizontal s h₀ l, horizontalDeletion_first_vertical s h₀ l,
    hcast]

/-- 概要：垂直始端の shuffle 面は第二の入力の最初の面を用いる（Berger–Fresse §1.1.3）。
方針：第一の座標を保存し、第二の座標を後続へ送る。
規約：元の shuffle の面は δ 0 である。
使われ方：第二の入力の最初の境界項を同定する。 -/
lemma shuffleSimplex_vertical_first_face (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath p (q + 1)) (h₀ : 0 ∉ s.val)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (simplicial (m + n)).δ 0 (shuffleSimplex m n i (p := p) (q := q + 1) s x y) =
      shuffleSimplex m n i (p := p) (q := q) ((verticalInsertionEquiv p q 0).symm ⟨s, h₀⟩) x
        ((simplicial n).δ 0 y) := by
  apply (simplexEquiv (m + n) (p + q)).injective
  funext k
  erw [simplexEquiv_δ (m + n) (p + q),
    simplexEquiv_shuffleSimplex m n i (p := p) (q := q + 1)]
  simp only [simplexEquiv_δ, simplexEquiv_shuffleSimplex, Fin.succAbove_zero]
  rw [verticalDeletion_first_horizontal s h₀ k, verticalDeletion_first_vertical s h₀ k]

end SerrePositivity.EInfinity.BarrattEccles
