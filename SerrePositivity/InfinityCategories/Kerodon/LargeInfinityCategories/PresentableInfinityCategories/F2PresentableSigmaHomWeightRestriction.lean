module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HomInfinityBifunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaHomWeightFamily
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaUniverseYoneda
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaYonedaInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomotopyLimitsPresentableSigmaHomWeightRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafHomWeights


/-!
概要：元の全自然変換空間族の Yoneda 制限を、元の大きい Yoneda の全族へ比較する。
方針：元の全 Yoneda 宇宙比較を反転・持ち上げし、同じ全共同 Hom と係数制限へ写す。
規約：全 C と全標的係数の自然同型を保持する。
使われ方：両右 Kan 族の元の制限の全自然比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の自然変換空間族の制限は、大きい元の Yoneda の全族と自然同型。 -/
def sigmaHomWeightFamily_restrictionIso
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaHomWeightFamily F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightFamily F₀) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorIso.ulift.{u + 2, u + 3} (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaUniverseYonedaIso C).op).postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      (pre ((SSet.uliftFunctor.{u + 3, u + 2}).map
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F₀))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 2})
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaHomWeightFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightFamily] using e

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
