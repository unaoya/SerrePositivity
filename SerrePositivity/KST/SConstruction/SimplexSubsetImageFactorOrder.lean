module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexSubsetInclusionOrder
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index

/-! # 元の任意の単調写像の像部分集合への番号因子
概要：単射性を仮定せず、元の部分集合の番号を同じ像部分集合の局所番号へ送る。
方針：元の像の昇順列挙の逆を使い、単調性と最小・最大頂点を回収する。
規約：像が二点以上の分岐を明記。使われ方：非単射な高次成分の低次元因子化。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.InfinityCategories

/-- 元の部分集合の番号を、同じ元の単調写像の像部分集合内の番号へ送る。 -/
def simplexSubsetImageFactorOrder {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card) :
    Fin (I.card - 1 + 1) →o Fin ((I.image α).card - 1 + 1) where
  toFun v := ((I.image α).orderIsoOfFin
    (show (I.image α).card = (I.image α).card - 1 + 1 by omega)).symm
      ⟨α (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v),
        Finset.mem_image.mpr ⟨_, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI v, rfl⟩⟩
  monotone' v w h := ((I.image α).orderIsoOfFin
    (show (I.image α).card = (I.image α).card - 1 + 1 by omega)).symm.monotone
      (α.monotone ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI).monotone h))

/-- 元の像番号を元の像部分集合で評価すると、同じ元の頂点像を回収する。 -/
lemma simplexSubsetImageFactorOrder_recovery {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card)
    (v : Fin (I.card - 1 + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder (I.image α) hJ (simplexSubsetImageFactorOrder α I hI hJ v) =
      α (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v) :=
  congrArg Subtype.val (((I.image α).orderIsoOfFin
    (show (I.image α).card = (I.image α).card - 1 + 1 by omega)).apply_symm_apply _)

/-- 元の像番号の因子は、元の始頂点番号を保つ。 -/
lemma simplexSubsetImageFactorOrder_first {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card) :
    simplexSubsetImageFactorOrder α I hI hJ 0 = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_injective (I.image α) hJ
  exact (simplexSubsetImageFactorOrder_recovery α I hI hJ 0).trans
    ((congrArg α (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_first I hI)).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (I.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ)).trans (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_first _ hJ).symm))

/-- 元の像番号の因子は、元の終頂点番号を保つ。 -/
lemma simplexSubsetImageFactorOrder_last {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card) :
    simplexSubsetImageFactorOrder α I hI hJ (Fin.last (I.card - 1)) =
      Fin.last ((I.image α).card - 1) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_injective (I.image α) hJ
  exact (simplexSubsetImageFactorOrder_recovery α I hI hJ _).trans
    ((congrArg α (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_last I hI)).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (I.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ)).trans (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_last _ hJ).symm))

end SerrePositivity.KST.SConstruction
