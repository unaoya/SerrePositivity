module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquarePostcomposeEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality
/-!
概要：全 dg 自然なホモトピー同値による終点後合成は同じ四角形の余極限性を保つ。
方針：指定後合成の coslice 辺を可逆とし、同じ全余錐の比較へ送る。
規約：通常の加群同型を仮定せず、元の二胞体を保持する。
使われ方：分裂 cone 射影から元の零ホモトピー四角形への cofiber 性の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {W X Y Z T : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

lemma isPushout_postcompose_of_homotopy (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A D W X Y Z)
    (q : Z ⟶ T) (hq : IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).map q))
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare s.square) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (s.postcompose q).square := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_homotopy A D q hq
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D q).toTruncated :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
      (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D q).toTruncated)
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)
    (s.postcomposeSliceEdge_projection q)).mpr he
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square)) (s.postcomposeSliceEdge q) hp
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (s.postcomposeCocone q) :=
    hs.of_vertexIso (asIso (SSet.Truncated.HomotopyCategory.homMk
      (s.postcomposeSliceEdge q)))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq (s.postcomposeCocone q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (s.postcompose q).square) rfl).mp hc

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (isPushout_postcompose_of_homotopy)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
