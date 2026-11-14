module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Triangles.DGModuleTriangleFunctor

/-! # dg 加群四角形の実関手像

概要：dg 関手は四辺・対角・二つの全 Hom end 成分を持つ実四角形を送る。
方針：各三角形で全成分の一致を使い、正方形の二セル表示で貼る。
規約：native nerve の写像では対象宇宙を共通にする。使われ方：cone の実関手像の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {W X Y Z : ModuleCategory A D} (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A D W X Y Z)

/-- 全 Hom end の成分を同時に送った実加群四角形データ。 -/
def map {E : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (_root_.SerrePositivity.DifferentialGraded.RightModule A E)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A E (F.onClosed.obj W) (F.onClosed.obj X)
      (F.onClosed.obj Y) (F.onClosed.obj Z) where
  bottom := F.onClosed.map s.bottom
  left := F.onClosed.map s.left
  right := F.onClosed.map s.right
  top := F.onClosed.map s.top
  diagonal := F.onClosed.map s.diagonal
  lowerHomotopy := (F.map (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Z)).f (-1) s.lowerHomotopy
  upperHomotopy := (F.map (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Z)).f (-1) s.upperHomotopy
  lowerEquation := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangle_map_differential A D E F _ _ _ _ s.lowerEquation
  upperEquation := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangle_map_differential A D E F _ _ _ _ s.upperEquation

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (map)


/-- 下側の実二単体は同じ関手による像。 -/
lemma map_lowerTriangle {E : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (_root_.SerrePositivity.DifferentialGraded.RightModule A E)) :
    s.lowerTriangle.map F = (s.map F).lowerTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_map A D E F _ _ _ _ s.lowerEquation

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (map_lowerTriangle)


/-- 上側の実二単体も同じ関手による像。 -/
lemma map_upperTriangle {E : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (_root_.SerrePositivity.DifferentialGraded.RightModule A E)) :
    s.upperTriangle.map F = (s.map F).upperTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct_map A D E F _ _ _ _ s.upperEquation

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (map_upperTriangle)


/-- 全四角形の実写像は dg nerve の native な後合成と一致する。 -/
lemma map_square {E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (_root_.SerrePositivity.DifferentialGraded.RightModule A E)) :
    (s.map F).square = s.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_upper, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_upper, SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm (s.map_upperTriangle F).symm
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_lower, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_lower, SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm (s.map_lowerTriangle F).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (map_square)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
