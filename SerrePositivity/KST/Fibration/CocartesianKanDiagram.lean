module
public import SerrePositivity.KST.Fibration.WeakHomotopyAnodyneComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.StrictKanCompletion
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianStrictTransportEquivalence

/-! # cocartesian section の厳密な輸送の空間値図式と同じ fiber の比較 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の全 cocartesian section による厳密輸送を、関手的な Kan 亜群化へ送る。 -/
def cocartesianKanDiagram {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion

/-- 同じ厳密図式を全単体上の coherent な空間値図式として保持する。 -/
def cocartesianKanCoherentDiagram {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (cocartesianKanDiagram p)

/-- 同じ恒等射評価を Kan 置換した、図式の各値から元の fiber の Kan 模型への実射。 -/
def cocartesianKanDiagramFiberComparison {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) (c : I) :
    ((cocartesianKanDiagram p).obj c).obj ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate p c)

/-- 全 section の恒等射評価の ∞ 圏同値から、同じ Kan 値比較も実際の同値となる。 -/
theorem cocartesianKanDiagramFiberComparison_isQCatEquivalence
    {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (c : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianKanDiagramFiberComparison p c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion_map_isQCatEquivalence
  exact weakHomotopyEquivalence_anodyneQ_isIso _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate_isQCatEquivalence p c).isWeakHomotopyEquivalence

end SerrePositivity.KST.Fibration
