module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.Simplices
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleFirstFace

/-!
# 一般 shuffle 単体の面の比較

概要：Berger–Fresse §1.1.3 の経路の座標公式を一般の単体集合の面へ移す。
方針：座標写像の合成の等式を単体集合の関手性で引き戻す。
規約：nerve の頂点による単体の判定は使わない。
使われ方：一般 shuffle の Leibniz 則の同方向の面。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

/-- 概要：二つの座標写像の合成の一致から shuffle の引き戻しを比較する（BF §1.1.3）。
方針：積の二成分で単体集合の関手性を使う。
規約：入力の面・退化と出力の面・退化の全てを許す。
使われ方：経路の座標公式を一般の単体の等式へ移す共通補題。 -/
lemma simplex_map_comparison (X Y : SSet.{0}) {p q p' q' : ℕ}
    (s : ShufflePath p q) (t : ShufflePath p' q')
    (f : ⦋p' + q'⦌ ⟶ ⦋p + q⦌) (g : ⦋p'⦌ ⟶ ⦋p⦌) (h : ⦋q'⦌ ⟶ ⦋q⦌)
    (hh : f ≫ s.horizontalMap = t.horizontalMap ≫ g)
    (hv : f ≫ s.verticalMap = t.verticalMap ≫ h)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    (X ⊗ Y).map f.op (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y t (X.map g.op x) (Y.map h.op y) := by
  apply Prod.ext
  · change X.map f.op (X.map s.horizontalMap.op x) =
      X.map t.horizontalMap.op (X.map g.op x)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
      ← op_comp, hh]
  · change Y.map f.op (Y.map s.verticalMap.op y) =
      Y.map t.verticalMap.op (Y.map h.op y)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
      ← op_comp, hv]

/-- 概要：水平な内部面は第一の入力の面との小さい shuffle（BF §1.1.3）。
方針：水平辺の削除の二座標公式で単体圏の射の合成を比較する。
規約：a,b は連続する水平辺。
使われ方：Leibniz 則の第一の入力の内部微分項。 -/
lemma simplex_horizontal_face (X Y : SSet.{0}) {p q : ℕ}
    (s : ShufflePath (p + 1) q) (a b : Fin (p + 1 + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    (X ⊗ Y).map (horizontalFaceMap p q a).op (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩)
        (X.δ (s.horizontal a.succ) x) y := by
  simpa! only [op_id, Functor.map_id_apply, SimplicialObject.δ_def] using
    _root_.SerrePositivity.SimplicialChains.Shuffle.simplex_map_comparison X Y s _ (horizontalFaceMap p q a)
      (SimplexCategory.δ (s.horizontal a.succ)) (𝟙 _) (by
        ext k : 3
        exact horizontalDeletion_horizontal s a b hab ha hb _) (by
        ext k : 3
        exact horizontalDeletion_vertical s a ha _) x y

/-- 概要：垂直な内部面は第二の入力の面との小さい shuffle（BF §1.1.3）。
方針：垂直辺の削除の二座標公式を合成の一致へ移す。
規約：a,b は連続する垂直辺。
使われ方：Leibniz 則の第二の入力の内部微分項。 -/
lemma simplex_vertical_face (X Y : SSet.{0}) {p q : ℕ}
    (s : ShufflePath p (q + 1)) (a b : Fin (p + (q + 1)))
    (hab : b.val = a.val + 1) (ha : a ∉ s.val) (hb : b ∉ s.val)
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    (X ⊗ Y).δ a.succ (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) s x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩) x
        (Y.δ (s.vertical a.succ) y) := by
  have he := _root_.SerrePositivity.SimplicialChains.Shuffle.simplex_map_comparison X Y s _ (SimplexCategory.δ a.succ)
      (𝟙 _) (SimplexCategory.δ (s.vertical a.succ)) (by
        ext k : 3
        exact verticalDeletion_horizontal s a ha k) (by
        ext k : 3
        exact verticalDeletion_vertical s a b hab ha hb k) x y
  simp only [op_id, Functor.map_id_apply] at he
  convert he using 1 <;> rfl

end SerrePositivity.SimplicialChains.Shuffle
