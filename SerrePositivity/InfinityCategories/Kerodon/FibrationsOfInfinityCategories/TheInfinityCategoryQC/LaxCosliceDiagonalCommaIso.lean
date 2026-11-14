module

public import Mathlib.CategoryTheory.Yoneda
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SliceComparison.LaxCoslice
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitComma
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxCosliceDiagonalComma

/-!
概要：太い coslice と対角関手の固定始域 comma は単体集合として同型。
方針：任意のパラメータの族の自然な全単射に Yoneda を適用する。
規約：充填性の仮定なし。実際の自然変換を持つ comma を使う。
使われ方：標準 comma の弱可縮性と対角関手の cofinality。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：太い coslice と対角 comma の単体集合の同型。
方針：全てのパラメータの族の全単射と前合成自然性を使う。
規約：頂点だけの比較に限定しない。使われ方：comma の模型を厳密に交換する。 -/
def laxCosliceDiagonalCommaIso {K C : SSet.{u}} (p : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) :=
  Yoneda.ext _ _
    (fun {A} f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxCosliceDiagonalCommaHomEquiv p A f)
    (fun {A} f ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxCosliceDiagonalCommaHomEquiv p A).symm f)
    (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxCosliceDiagonalCommaHomEquiv p _).symm_apply_apply f)
    (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxCosliceDiagonalCommaHomEquiv p _).apply_symm_apply f)
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxCosliceDiagonalCommaHomEquiv_naturality

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
