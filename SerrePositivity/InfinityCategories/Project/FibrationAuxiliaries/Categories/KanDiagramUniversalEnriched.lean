module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramOppositeComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramEvaluation

/-!
概要：全 strict Kan 図式の評価を、一つの豊穣図式へ束ねる。
方針：各対象の評価関手と、strict な変換空間の全単体の自然性を使う。
規約：変換空間の Kan 性を仮定せず、全 Hom パラメーターを保つ。
使われ方：反転図式の全対象・全高次の変換を同じ共通解像上で実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 底の射による評価の比較は、全 strict 変換パラメーターに豊穣自然。 -/
def kanDiagramEvaluationComparison {I : Type u} [SmallCategory I] {i j : I} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched j) := by
  refine ⟨fun F => F.val.map f, ?_⟩
  intro F G
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  exact (t.property f n (𝟙 n) x).symm

/-- 全 strict Kan 図式を、元の底全体と全 Hom に自然な一つの豊穣図式として表す。 -/
def kanDiagramUniversalEnriched (I : Type u) [SmallCategory I] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) I where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched i
  map f := kanDiagramEvaluationComparison f
  map_id i F := F.val.map_id i
  map_comp f g F := F.val.map_comp f g

/-- 普遍豊穣図式を一つの対象で評価すると、指定された元の strict 図式そのもの。 -/
lemma kanDiagramUniversalEnriched_evaluate {I : Type u} [SmallCategory I]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) : (kanDiagramUniversalEnriched I).evaluate F = F.val := rfl

/-- 普遍豊穣図式の高次 Hom の作用は、元の strict 変換空間の恒等射。 -/
lemma kanDiagramUniversalEnriched_toEnrichedFunctor (I : Type u) [SmallCategory I] :
    (kanDiagramUniversalEnriched I).toEnrichedFunctor =
      EnrichedFunctor.id SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) := by
  refine EnrichedFunctor.ext SSet (fun F => rfl) ?_
  intro F G
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
