module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCommonMapSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareFunctor
/-!
概要：独立の係数圏宇宙を持つ dg 加群四角形の実関手像を共通宇宙で同定する。
方針：既存の混在宇宙の二つの合成三角形の比較を、正方形の二セルで貼る。
規約：四辺・対角・両次数 −1 成分を変えない。
使われ方：全加群間の dg 関手の混在宇宙での cone 保存。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {C : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  {W X Y Z : ModuleCategory R D} (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData R D W X Y Z)

lemma map_square_common (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R C)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{max (u + 1) v, max (u + 1) v w t} s.square ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) w, t} F =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{max (u + 1) w, max (u + 1) v w t} (s.map F).square := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.uliftSquare_triangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_upper,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.uliftSquare_triangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_upper, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_simplex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.map_upperTriangle]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.uliftSquare_triangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_lower,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.uliftSquare_triangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_lower, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_simplex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.map_lowerTriangle]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (map_square_common)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
