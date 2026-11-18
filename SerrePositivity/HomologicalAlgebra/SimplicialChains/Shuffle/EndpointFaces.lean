module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.FaceComparison

/-!
# 一般 shuffle 単体の両端の面

概要：Berger–Fresse §1.1.3 の始端・終端の面を二つの入力の面で表す。
方針：先頭・末尾の辺を削除した座標公式を単体圏の射の合成へ移す。
規約：水平端点と垂直端点を、それぞれの入力の δ 0・δ last へ対応させる。
使われ方：一般 shuffle の微分の両端の境界項。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

/-- 概要：水平始端の面は第一の入力の最初の面（BF §1.1.3）。
方針：削除後の水平座標は後続値、垂直座標は同じ値となる公式を使う。
規約：出力の面写像の次数移送を明示する。
使われ方：第一の入力の最初の境界項。 -/
lemma simplex_horizontal_first_face (X Y : SSet.{0}) {p q : ℕ}
    (s : ShufflePath (p + 1) q) (h₀ : 0 ∈ s.val)
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    (X ⊗ Y).map (horizontalFirstFaceMap p q).op (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y ((horizontalInsertionEquiv p q 0).symm ⟨s, h₀⟩) (X.δ 0 x) y := by
  simpa only [op_id, Functor.map_id_apply, SimplicialObject.δ_def] using
    _root_.SerrePositivity.SimplicialChains.Shuffle.simplex_map_comparison X Y s _ (horizontalFirstFaceMap p q)
      (SimplexCategory.δ 0) (𝟙 _) (by
        ext k : 3
        change s.horizontal (Fin.cast (by omega : p + q + 1 = p + 1 + q) k).succ =
          (0 : Fin (p + 2)).succAbove _
        rw [Fin.succAbove_zero]
        exact horizontalDeletion_first_horizontal s h₀ _) (by
        ext k : 3
        exact horizontalDeletion_first_vertical s h₀ _) x y

/-- 概要：垂直始端の面は第二の入力の最初の面（BF §1.1.3）。
方針：削除後の水平座標を保ち、垂直座標を後続値へ送る。
規約：出力の最初の面は δ 0。
使われ方：第二の入力の最初の境界項。 -/
lemma simplex_vertical_first_face (X Y : SSet.{0}) {p q : ℕ}
    (s : ShufflePath p (q + 1)) (h₀ : 0 ∉ s.val)
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    (X ⊗ Y).δ 0 (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) s x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y ((verticalInsertionEquiv p q 0).symm ⟨s, h₀⟩) x (Y.δ 0 y) := by
  have he := _root_.SerrePositivity.SimplicialChains.Shuffle.simplex_map_comparison X Y s _ (SimplexCategory.δ 0) (𝟙 _) (SimplexCategory.δ 0) (by
      ext k : 3
      change s.horizontal ((0 : Fin (p + q + 2)).succAbove k) = _
      rw [Fin.succAbove_zero]
      exact verticalDeletion_first_horizontal s h₀ k) (by
      ext k : 3
      change s.vertical ((0 : Fin (p + q + 2)).succAbove k) =
        (0 : Fin (q + 2)).succAbove _
      rw [Fin.succAbove_zero, Fin.succAbove_zero]
      exact verticalDeletion_first_vertical s h₀ k) x y
  simp only [op_id, Functor.map_id_apply] at he
  convert he using 1 <;> rfl

/-- 概要：水平終端の面は第一の入力の最後の面（BF §1.1.3）。
方針：末尾の水平辺の削除の座標公式を用いる。
規約：a は最後の辺。
使われ方：第一の入力の最後の境界項。 -/
lemma simplex_horizontal_last_face (X Y : SSet.{0}) {p q : ℕ}
    (s : ShufflePath (p + 1) q) (a : Fin (p + 1 + q)) (ha : a ∈ s.val)
    (hlast : a.val + 1 = p + 1 + q) (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    (X ⊗ Y).map (horizontalFaceMap p q a).op (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩)
        (X.δ (Fin.last (p + 1)) x) y := by
  simpa only [op_id, Functor.map_id_apply, SimplicialObject.δ_def] using
    _root_.SerrePositivity.SimplicialChains.Shuffle.simplex_map_comparison X Y s _ (horizontalFaceMap p q a)
      (SimplexCategory.δ (Fin.last (p + 1))) (𝟙 _) (by
        ext k : 3
        exact horizontalDeletion_last s a ha hlast _) (by
        ext k : 3
        exact horizontalDeletion_vertical s a ha _) x y

/-- 概要：垂直終端の面は第二の入力の最後の面（BF §1.1.3）。
方針：水平座標の保存と末尾の垂直座標の公式を用いる。
規約：a は最後の辺。
使われ方：第二の入力の最後の境界項。 -/
lemma simplex_vertical_last_face (X Y : SSet.{0}) {p q : ℕ}
    (s : ShufflePath p (q + 1)) (a : Fin (p + (q + 1))) (ha : a ∉ s.val)
    (hlast : a.val + 1 = p + (q + 1)) (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    (X ⊗ Y).δ a.succ (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) s x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩) x
        (Y.δ (Fin.last (q + 1)) y) := by
  have he := _root_.SerrePositivity.SimplicialChains.Shuffle.simplex_map_comparison X Y s _ (SimplexCategory.δ a.succ)
      (𝟙 _) (SimplexCategory.δ (Fin.last (q + 1))) (by
        ext k : 3
        exact verticalDeletion_horizontal s a ha k) (by
        ext k : 3
        exact verticalDeletion_last s a ha hlast k) x y
  simp only [op_id, Functor.map_id_apply] at he
  convert he using 1 <;> rfl

end SerrePositivity.SimplicialChains.Shuffle
