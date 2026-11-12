module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitAugmentation

/-! # 元の左右分割 necklace の次元と HA 次数
概要：元の左右フィルターの実 necklace の次元と、合成項の HA 次数を同定する。
方針：元の bead 次元と元の左右濃度の和を使う。
規約：元の実 necklace と共有頂点を保持。使われ方：native HA 合成項の次数移送。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.InfinityCategories

/-- 元の左分割 necklace の次元は、同じ元の左部分集合の濃度から二を除いた値。 -/
lemma necklaceInSimplexSubsetSplitLeft_dimension {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) :
    (necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL).necklace.down.dimension =
      (I.filter (· ≤ j)).card - 2 :=
  necklaceInSimplexSubset_dimension.{u} (I.filter (· ≤ j)) hL

/-- 元の右分割 necklace の次元は、同じ元の右部分集合の濃度から二を除いた値。 -/
lemma necklaceInSimplexSubsetSplitRight_dimension {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (necklaceInSimplexSubsetSplitRight.{u} I hI j hj hR).necklace.down.dimension =
      (I.filter (j ≤ ·)).card - 2 :=
  necklaceInSimplexSubset_dimension.{u} (I.filter (j ≤ ·)) hR

/-- 元の左右実 necklace の合計次元の負値は、元の HA 成分次数に一を加えた値。 -/
lemma simplexSubsetSplit_degree {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    -(((necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL).necklace.down.dimension +
      (necklaceInSimplexSubsetSplitRight.{u} I hI j hj hR).necklace.down.dimension : ℕ) : ℤ) =
      (2 - (I.card : ℤ)) + 1 := by
  have hl := necklaceInSimplexSubsetSplitLeft_dimension.{u} I hI j hj hL
  have hr := necklaceInSimplexSubsetSplitRight_dimension.{u} I hI j hj hR
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
  omega

end SerrePositivity.KST.SConstruction
