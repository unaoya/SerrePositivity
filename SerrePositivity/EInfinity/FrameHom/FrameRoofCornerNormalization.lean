module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofSliceFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.VertexFiberNervePullback

/-!
# 実屋根 corner の元の Over 次数による正規化

概要：元の指定点の全 corner を、同じ次数へ向かう矢の nerve 上で表示する。
方針：既存の全 slice 同型で引き戻しを同型にし、同じ恒等射上の fiber を回収する。
規約：元の点・元の屋根射影・元の次数を保つ。
使われ方：corner 全体から同じ指定次数の写像空間への実評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)

abbrev roofCornerNormalized := pullback (roofTargetProjection A Y q)
  (nerveMap (Over.forget (roofTargetDegree A Y q b)))

abbrev roofCornerNormalizedProjection : roofCornerNormalized A Y q b ⟶
    nerve (Over (roofTargetDegree A Y q b)) := pullback.snd _ _

def roofCornerNormalizationMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (roofTargetProjection A Y q) ⟶
      roofCornerNormalized A Y q b :=
  pullback.map _ _ _ _ (roofTargetDegreeSliceIso A Y q b).hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using (roofTargetDegreeSliceIso_projection A Y q b).symm)
    (by simp) ≫ (pullbackSymmetry _ _).hom

instance roofCornerNormalizationMap_isIso : IsIso (roofCornerNormalizationMap A Y q b) := by
  dsimp only [roofCornerNormalizationMap]
  infer_instance

lemma roofCornerNormalizationMap_source : roofCornerNormalizationMap A Y q b ≫
    pullback.fst _ _ = pullback.snd _ _ := by
  simp only [roofCornerNormalizationMap, Category.assoc, pullbackSymmetry_hom_comp_fst,
    pullback.map, pullback.lift_snd, Category.comp_id]

lemma roofCornerNormalizationMap_over : roofCornerNormalizationMap A Y q b ≫
    roofCornerNormalizedProjection A Y q b =
      pullback.fst _ _ ≫ (roofTargetDegreeSliceIso A Y q b).hom := by
  simp only [roofCornerNormalizationMap, roofCornerNormalizedProjection, Category.assoc,
    pullbackSymmetry_hom_comp_snd, pullback.map, pullback.lift_fst]

lemma roofCornerNormalizedProjection_leftFibration [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (roofTargetProjection A Y q)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (roofCornerNormalizedProjection A Y q b) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := roofTargetProjection A Y q))⟩

def roofCornerTerminal : (nerve (Over (roofTargetDegree A Y q b))) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Over.mk (𝟙 (roofTargetDegree A Y q b)))

lemma roofCornerTerminal_isTerminal : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (roofCornerTerminal A Y q b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveVertex_isTerminal Over.mkIdTerminal

def roofCornerTerminalFiberIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (roofCornerNormalizedProjection A Y q b) (roofCornerTerminal A Y q b) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (roofTargetProjection A Y q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (roofTargetDegree A Y q b)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberNervePullbackIso (roofTargetProjection A Y q)
    (Over.forget (roofTargetDegree A Y q b)) (Over.mk (𝟙 (roofTargetDegree A Y q b)))

lemma roofCornerTerminalFiberIso_source : (roofCornerTerminalFiberIso A Y q b).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (roofTargetProjection A Y q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (roofTargetDegree A Y q b)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (roofCornerNormalizedProjection A Y q b) (roofCornerTerminal A Y q b) ≫
        pullback.fst _ _ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberNervePullbackIso_hom_ι _ _ _

end SerrePositivity.EInfinity.FrameHom.FrameArrows
