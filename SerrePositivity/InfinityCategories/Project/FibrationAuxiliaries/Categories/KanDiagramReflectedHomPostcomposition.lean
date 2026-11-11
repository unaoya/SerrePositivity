module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.KanDiagramHomPostcomposition
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeInternalHomEvaluation

/-!
概要：表現可能 Hom 図式の全後合成を反転し、係数の同時評価の厳密な式を与える。
方針：一成分の式と内部 Hom の反転同型の uncurry を使う。
規約：元の全変換のパラメーターを保持する。
使われ方：左切断 prism の終点の係数を実際の weighted 作用へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories


/-- 全後合成を一成分で評価すると、元の変換の同じ成分への後合成そのもの。 -/
lemma kanDiagramHomPostcomposition_component {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramHomPostcomposition F G x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram G.val x) i =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i ≫
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramHomPostcompositionComponent F G x i := rfl

/-- 表現可能 Hom 図式の後合成を、反転した係数図式間の全変換へ移す。 -/
def kanDiagramReflectedHomPostcomposition {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SimplicialCategory.sHom F G).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram G.val x ⋙ SSet.opFunctor) :=
  SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramHomPostcomposition F G x) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictDiagramOppositeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram G.val x)

/-- 反転した後合成の一成分は、元の後合成の成分と同じ反転内部 Hom の同型の合成。 -/
lemma kanDiagramReflectedHomPostcomposition_component {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (i : I) :
    kanDiagramReflectedHomPostcomposition F G x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram G.val x ⋙ SSet.opFunctor) i =
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
      (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i) ≫
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramHomPostcompositionComponent F G x i) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (SimplicialCategory.sHom x (F.val.obj i))
          (SimplicialCategory.sHom x (G.val.obj i))).hom := by
  rw [kanDiagramReflectedHomPostcomposition, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictDiagramOppositeHom_component, ← Category.assoc, ← SSet.opFunctor.map_comp,
    kanDiagramHomPostcomposition_component, SSet.opFunctor.map_comp, Category.assoc]
  rfl

/-- 反転した全後合成の実際の評価は、元の二係数を反転側で豊穣合成する同じ射。 -/
lemma kanDiagramReflectedHomPostcomposition_uncurry {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (i : I) :
    uncurry (kanDiagramReflectedHomPostcomposition F G x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram G.val x ⋙ SSet.opFunctor) i) =
    ((SimplicialCategory.sHom x (F.val.obj i)).op ◁ SSet.opFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso (SimplicialCategory.sHom x (F.val.obj i))
        (SimplicialCategory.sHom (F.val.obj i) (G.val.obj i))).hom ≫
      SSet.opFunctor.map (eComp SSet x (F.val.obj i) (G.val.obj i)) := by
  rw [kanDiagramReflectedHomPostcomposition_component, ← Category.assoc,
    ← SSet.opFunctor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHom_map_uncurry,
    uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramHomPostcompositionComponent, uncurry_curry,
    SSet.opFunctor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
