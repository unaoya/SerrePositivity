module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanJoinCells

/-! # 最初の三頂点の順序写像

概要：span の標準セルの最初の三頂点を三角形として選び、最後の面との合成を計算する。
方針：自然数の値を保つ単調写像を使う。
規約：先頭三点は固定二点と最初の可変点。使われ方：D7 の指定余錐の三角形の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

/-- 概要：最初の三頂点の包含は有限添字の値を保つ。
方針：三点の番号をそのまま含める。
規約：全次元。使われ方：余錐の三角形の指定。 -/
def firstTriangleOrderHom (n : ℕ) : Fin 3 →o Fin (n + 3) where
  toFun i := ⟨i.val, by have := i.isLt; omega⟩
  monotone' _ _ h := h

/-- 概要：最初の三頂点は最後の面を経由して回収できる。
方針：最後の点を飛ばす写像が castSucc であることを使う。
規約：一つ大きいセルでも最初の三点の値は保つ。使われ方：既知の最後の面からの回収。 -/
lemma firstTriangleOrderHom_face_last (n : ℕ) :
    (Fin.last (n + 3)).succAboveOrderEmb.toOrderHom.comp (firstTriangleOrderHom n) =
      firstTriangleOrderHom (n + 1) := by
  apply DFunLike.ext
  intro i
  change (Fin.last (n + 3)).succAbove (firstTriangleOrderHom n i) =
    firstTriangleOrderHom (n + 1) i
  rw [Fin.succAbove_last]
  rfl

/-- 概要：最初の三頂点の包含は単射。
方針：値が変わらないことを使う。
規約：全次元。使われ方：辺と三点成分の単射による比較。 -/
lemma firstTriangleOrderHom_injective (n : ℕ) : Function.Injective (firstTriangleOrderHom n) := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin (n + 3) => z.val) h)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
