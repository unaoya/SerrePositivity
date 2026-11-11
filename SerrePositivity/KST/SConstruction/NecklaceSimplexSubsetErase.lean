module
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubsetAt
public import SerrePositivity.KST.SConstruction.SimplexSubsetInclusionCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index

/-! # 元の内部点削除の実 necklace 射と零座標
概要：元の内部点を削った部分集合 bead から元の bead への同端点の実可換三角形を作る。
方針：native HA の削除の端点補題と、元の部分集合包含・全ファイバー座標を使う。
規約：元の両端・全高次単体・生成射を保持。使われ方：HA 削除項の元の零面への接続。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.InfinityCategories
variable {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1))
  (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
  (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))

include hI hjm hjM in
/-- 元の厳密な内部点を消しても、元の両端の二点が残る。 -/
lemma simplexSubsetErase_two : 2 ≤ (I.erase j).card :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two (I.min'_mem _) (I.max'_mem _) hjm hjM

/-- 元の内部点削除は、元の最小端点を保つ。 -/
lemma simplexSubsetErase_min :
    (I.erase j).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ (simplexSubsetErase_two I hI j hjm hjM)) =
      I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min (I.isLeast_min' _) hjm _).symm

/-- 元の内部点削除は、元の最大端点を保つ。 -/
lemma simplexSubsetErase_max :
    (I.erase j).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ (simplexSubsetErase_two I hI j hjm hjM)) =
      I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max (I.isGreatest_max' _) hjM _).symm

/-- 元の内部点削除の、元の同じ両端の Hom 図式内の実 necklace 可換三角形。 -/
def necklaceInSimplexSubsetErase :
    necklaceInSimplexSubsetAt.{u} (I.erase j) (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (simplexSubsetErase_two I hI j hjm hjM)
        (simplexSubsetErase_min I hI j hjm hjM).symm
        (simplexSubsetErase_max I hI j hjm hjM).symm ⟶ necklaceInSimplexSubset I hI :=
  necklaceInSimplexSubsetAtInclusion (I.erase j) I _ _
    (simplexSubsetErase_two I hI j hjm hjM) hI (Finset.erase_subset _ _)
    (simplexSubsetErase_min I hI j hjm hjM).symm
    (simplexSubsetErase_max I hI j hjm hjM).symm rfl rfl

/-- 元の内部点削除は、同じ元の Hom の cubical 生成射の表示関係を与える。 -/
lemma necklaceInSimplexSubsetErase_cell :
    necklaceCubicalSet.map (necklaceInSimplexSubsetErase.{u} I hI j hjm hjM).necklaceHom ≫
        necklaceCubicalCell (necklaceInSimplexSubset I hI) =
      necklaceCubicalCell
        (necklaceInSimplexSubsetAt (I.erase j) (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
          (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (simplexSubsetErase_two I hI j hjm hjM)
          (simplexSubsetErase_min I hI j hjm hjM).symm
          (simplexSubsetErase_max I hI j hjm hjM).symm) :=
  necklaceCubicalCell_relation (necklaceInSimplexSubsetErase I hI j hjm hjM)

/-- 元の削除された所属内部頂点の出力座標は、元の全入力 Bool 座標に対して零。 -/
lemma necklaceInSimplexSubsetErase_coordinate_zero (hj : j ∈ I)
    (x : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.erase j).card - 1)).NonjointVertex → Bool) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap (necklaceInSimplexSubsetErase.{u} I hI j hjm hjM).necklaceHom x
      (simplexSubsetInteriorVertex I hI j hj hjm hjM) = false :=
  simplexSubsetInclusion_coordinate_missing (I.erase j) I
    (simplexSubsetErase_two I hI j hjm hjM) hI (Finset.erase_subset _ _)
    (simplexSubsetErase_min I hI j hjm hjM) (simplexSubsetErase_max I hI j hjm hjM)
    x j hj (fun h => (Finset.mem_erase.mp h).1 rfl) hjm hjM

end SerrePositivity.KST.SConstruction
