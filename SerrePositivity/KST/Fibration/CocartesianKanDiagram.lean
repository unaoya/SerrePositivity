module
public import SerrePositivity.KST.Fibration.StrictKanCompletion
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianStrictTransportEquivalence

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
    (p : E ⟶ nerve I) : I ⥤ KanObject.{u} :=
  kanCocartesianStrictTransportDiagram p ⋙ strictKanCompletion

/-- 同じ厳密図式を全単体上の coherent な空間値図式として保持する。 -/
def cocartesianKanCoherentDiagram {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u} :=
  kanDiagramCoherentNerve (cocartesianKanDiagram p)

/-- 同じ恒等射評価を Kan 置換した、図式の各値から元の fiber の Kan 模型への実射。 -/
def cocartesianKanDiagramFiberComparison {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) (c : I) :
    ((cocartesianKanDiagram p).obj c).obj ⟶
      (strictKanCompletion.obj (vertexFiber p (nerveVertex c))).obj :=
  strictKanCompletion.map (kanCocartesianStrictTransportEvaluate p c)

/-- 全 section の恒等射評価の ∞ 圏同値から、同じ Kan 値比較も実際の同値となる。 -/
theorem cocartesianKanDiagramFiberComparison_isQCatEquivalence
    {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [CocartesianFibration p] (c : I) :
    IsQCatEquivalence (cocartesianKanDiagramFiberComparison p c) := by
  apply strictKanCompletion_map_isQCatEquivalence
  exact weakHomotopyEquivalence_anodyneQ_isIso _
    (kanCocartesianStrictTransportEvaluate_isQCatEquivalence p c).isWeakHomotopyEquivalence

end SerrePositivity.KST.Fibration
