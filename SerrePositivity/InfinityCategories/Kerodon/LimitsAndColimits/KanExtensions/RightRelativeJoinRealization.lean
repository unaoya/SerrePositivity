module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightCylinder

/-!
概要：任意の右指定変換を relative join 上の図式で表示する。
方針：反転した左側の表示を二重反転の同型で元へ戻し、一つの円柱比較を保持する。
規約：δ は任意。端点の厳密化と指定変換の類の保存は別工程。
使われ方：右 Kan 拡張の相対 join の局所極限表示への還元。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：円柱全体との同型を持つ右相対 join 表示。
方針：反転模型の右円柱上で、元の α と F を保持した一つの比較を指定する。
規約：独立な端点同型の組で代用しない。
使われ方：端点補正後の右指定変換の類を追跡する。 -/
structure RightKanRelativeJoinRealization {K C D : SSet.{u}}
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀) where
  diagram : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ ⟶ D
  comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightRelativeJoinCylinderComparison δ ≫ diagram)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCylinderDiagram δ F₀ F α)

/-- 概要：任意の右指定変換には一つの円柱比較を持つ右相対 join 表示が存在する。
方針：反転した左指定変換の表示を取り、その円柱比較の逆を反転して元へ戻す。
規約：D のみ quasicategory、δ 自体の単射性は不要。
使われ方：任意の α を右相対 join 上の図式へ移す。 -/
lemma rightKanRelativeJoinRealization_nonempty {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀) :
    Nonempty (RightKanRelativeJoinRealization δ F₀ F α) := by
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanRelativeJoinRealization_nonempty
    (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀) (SSet.opFunctor.map F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanOppositeTransformation δ F₀ F α)
  let G := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightDualIso δ).inv ≫ SSet.opFunctor.map s.diagram ≫
    (SSet.opFunctorCompOpFunctorIso.app D).hom
  have e := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoOpposite s.comparison.symm).postcomp
    (SSet.opFunctorCompOpFunctorIso.app D).hom
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightRelativeJoinCylinderComparison δ ≫ G =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (SSet.opFunctor.map δ) ≫ s.diagram) ≫
        (SSet.opFunctorCompOpFunctorIso.app D).hom := by
    simp only [G, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightRelativeJoinCylinderComparison, Category.assoc,
      Iso.hom_inv_id_assoc, CategoryTheory.Functor.map_comp]
  exact ⟨⟨G, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoTransport e hG.symm rfl⟩⟩

/-- 概要：右相対 join 表示の prism は元の α 全体と関手として同型。
方針：一つの円柱比較を prism 部分へ制限し、両図式の厳密な計算則を使う。
規約：始点と終点だけでなく全時間の比較。
使われ方：指定変換の類を保つ端点補正の準備。 -/
def RightKanRelativeJoinRealization.prismIso {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    (s : RightKanRelativeJoinRealization δ F₀ F α) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ ≫ s.diagram) α.h := by
  have e := s.comparison.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism δ)
  simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism_comparison,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism_diagram] using e

/-- 概要：右相対 join 表示の左端は元の F と同型。
方針：円柱全体の比較を底 C へ制限する。
規約：prism の比較と同じ円柱比較から得る。
使われ方：右側の二つの端点の同時の厳密化。 -/
def RightKanRelativeJoinRealization.leftIso {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    (s : RightKanRelativeJoinRealization δ F₀ F α) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ ≫ s.diagram) F := by
  have e := s.comparison.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderBase δ)
  simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderBase_comparison,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderBase_diagram] using e

/-- 概要：右相対 join 表示の右端は元の F₀ と同型。
方針：prism 全体の比較を終端へ制限する。
規約：端点での射の厳密な一致とは主張しない。
使われ方：元の F₀ と右相対 join の右端の比較。 -/
def RightKanRelativeJoinRealization.rightIso {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    (s : RightKanRelativeJoinRealization δ F₀ F α) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ ≫ s.diagram) F₀ := by
  have e := s.prismIso.precomp SSet.ι₁
  simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism_one, α.h₁] using e

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
