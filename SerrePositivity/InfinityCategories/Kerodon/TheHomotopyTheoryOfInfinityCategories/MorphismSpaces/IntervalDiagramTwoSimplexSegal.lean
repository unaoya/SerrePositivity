module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.InnerTwoHornHomPullbacks
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramAnodyneRestriction

/-!
概要：二次元単体上の分類先の区間 Hom を、二区間の同じ Hom の pullback と比較する。
方針：内ホーンへの元の自明 Kan 制限と、その厳密な pullback 表示を合成する。
規約：元の二図式と全パラメーターを固定する。
使われ方：元の分類 Hom 作用の二次元比較の標的。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces


variable {X : SSet.{u}} (F G : (Δ[2] : SSet.{u}) ⟶ X)

/-- 元のホーン制限を、同じ底上のホーンの端点で明示する。 -/
abbrev intervalDiagramTwoSimplexHornRestriction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.apex (horn 2 1).ι).hom ≫ F))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.apex (horn 2 1).ι).hom ≫ G)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction (horn 2 1).ι F G

/-- 元の二次元区間 Hom から、同じ二区間の Hom の厳密な pullback への比較。 -/
def intervalDiagramTwoSimplexSegalMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) ⟶
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.toSecond (horn 2 1).ι))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.toFirst (horn 2 1).ι)) :=
  intervalDiagramTwoSimplexHornRestriction F G ≫
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.InnerTwoHornOver.intervalDiagram_isPullback F G (horn 2 1).ι).isoPullback.hom

/-- 分類先の同じ二区間への比較も、全パラメーターで自明 Kan fibration。 -/
lemma intervalDiagramTwoSimplexSegalMap_trivialKanFibration [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (intervalDiagramTwoSimplexSegalMap F G) := by
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction_trivialKanFibration_of_innerAnodyne (horn 2 1).ι
      (innerAnodyneExtensions.horn_ι (by decide) (by decide)) F G).mem
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isIso _)⟩

/-- 最初の射影は、同じホーンから次の区間への元の区間 Hom の制限。 -/
lemma intervalDiagramTwoSimplexSegalMap_fst :
    intervalDiagramTwoSimplexSegalMap F G ≫
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.toSecond (horn 2 1).ι))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.toFirst (horn 2 1).ι)) =
      intervalDiagramTwoSimplexHornRestriction F G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.secondInclusion (horn 2 1).ι) := by
  exact (Category.assoc (intervalDiagramTwoSimplexHornRestriction F G) _ _).trans
    (congrArg (fun k ↦ intervalDiagramTwoSimplexHornRestriction F G ≫ k)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.InnerTwoHornOver.intervalDiagram_isPullback F G (horn 2 1).ι).isoPullback_hom_fst)

/-- 二番目の射影は、同じホーンから最初の区間への元の区間 Hom の制限。 -/
lemma intervalDiagramTwoSimplexSegalMap_snd :
    intervalDiagramTwoSimplexSegalMap F G ≫
        pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.toSecond (horn 2 1).ι))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.toFirst (horn 2 1).ι)) =
      intervalDiagramTwoSimplexHornRestriction F G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.firstInclusion (horn 2 1).ι) := by
  exact (Category.assoc (intervalDiagramTwoSimplexHornRestriction F G) _ _).trans
    (congrArg (fun k ↦ intervalDiagramTwoSimplexHornRestriction F G ≫ k)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.InnerTwoHornOver.intervalDiagram_isPullback F G (horn 2 1).ι).isoPullback_hom_snd)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
