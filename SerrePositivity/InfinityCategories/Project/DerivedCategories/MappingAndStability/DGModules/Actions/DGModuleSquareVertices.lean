module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareData
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.StandardCofiberSquare

/-! # 全 Hom end の実四角形の四頂点

概要：四角形データの実辺と四頂点を元の閉零射と実加群対象に同定する。
方針：二つの実二単体の面を評価する。
規約：零性や普遍性は仮定しない。使われ方：零角変更と関手同型の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {W X Y Z : ModuleCategory A D} (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A D W X Y Z)

/-- 下辺は元の閉零射の実辺。 -/
lemma square_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ s.square =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D s.bottom).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberSquareTriangle_bottomEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation).d₂

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (square_bottom)


/-- 左辺は元の閉零射の実辺。 -/
lemma square_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ s.square =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D s.left).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberSquareTriangle_leftEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D s.left s.top s.diagonal s.upperHomotopy s.upperEquation).d₂

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (square_left)


/-- 右辺は元の閉零射の実辺。 -/
lemma square_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ s.square =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D s.right).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation).d₀

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (square_right)


/-- 始点の実頂点。 -/
lemma square_vertex00 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) W) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source, square_bottom, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D s.bottom).src_eq

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (square_vertex00)


/-- 下辺終点の実頂点。 -/
lemma square_vertex10 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 1 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) X) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target, square_bottom, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D s.bottom).tgt_eq

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (square_vertex10)


/-- 左上の実頂点。 -/
lemma square_vertex01 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 0 1 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target, square_left, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D s.left).tgt_eq

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (square_vertex01)


/-- 終点の実頂点。 -/
lemma square_vertex11 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 1 1 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) Z) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target, square_right, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D s.right).tgt_eq

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (square_vertex11)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
