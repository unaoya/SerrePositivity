module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSimplexInclusions

/-! # 最後の三頂点の順序写像

概要：標準セルの最後の三頂点を三角形として選ぶ順序写像を記録する。
方針：番号に同じ自然数を加え、零番目の面との合成を値で比較する。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：最後の頂点に指定された錐の三角形の回収。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：最後の三頂点は番号 n,n+1,n+2 で与えられる。
方針：三点の各番号に n を加える単調写像を使う。
規約：HTT §1.2.13。使われ方：錐頂点と末尾二点からなる三角形の指定。 -/
def lastTriangleOrderHom (n : ℕ) : Fin 3 →o Fin (n + 3) where
  toFun i := ⟨n + i.val, by have := i.isLt; omega⟩
  monotone' _ _ h := Nat.add_le_add_left h n

/-- 概要：最後の三頂点の包含を零番目の面と合成すると、一つ大きいセルの最後の三頂点になる。
方針：零番目の点を飛ばす写像が後続写像であることを使う。
規約：HTT §1.2.13。使われ方：既知の零番目の面から錐の三角形のデータを回収する。 -/
lemma lastTriangleOrderHom_face_zero (n : ℕ) :
    (0 : Fin (n + 4)).succAboveOrderEmb.toOrderHom.comp (lastTriangleOrderHom n) =
      lastTriangleOrderHom (n + 1) := by
  apply DFunLike.ext
  intro i
  change (0 : Fin (n + 4)).succAbove (lastTriangleOrderHom n i) = lastTriangleOrderHom (n + 1) i
  rw [Fin.succAbove_zero]
  apply Fin.ext
  change n + i.val + 1 = n + 1 + i.val
  omega

/-- 概要：最後の三頂点の順序写像は単射。
方針：値に同じ自然数を加える写像の消去則を使う。
規約：HTT §1.2.13。使われ方：辺と三点成分の単射による制限の比較。 -/
lemma lastTriangleOrderHom_injective (n : ℕ) : Function.Injective (lastTriangleOrderHom n) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun z : Fin (n + 3) => z.val) h
  change n + i.val = n + j.val at hv
  omega

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
