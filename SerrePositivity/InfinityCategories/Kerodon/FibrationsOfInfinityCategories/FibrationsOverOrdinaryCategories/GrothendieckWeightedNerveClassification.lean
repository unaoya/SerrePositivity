module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveOver
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ClassificationTransport

/-!
概要：同じ底のGrothendieck・weighted nerve置換の全分類を比較する。
方針：検証済みのOver同型を忘却し、既存のleftClassification_overIsoを使う。
規約：分類は底全体のFunctorIso。元の係数とのKan比較はまだ主張しない。
使われ方：IS-W2 R03dの相対分類の比較の一方の端。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 同じ底上の二つの指定置換の分類は、底全体で一つの関手同型を持つ。 -/
def grothendieckWeightedNerveReplacementClassificationIso :
    FunctorIso
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (weightedNerveProjection (F ⋙ nerveFunctor)))).hom) :=
  leftClassification_overIso _ _
    ((Over.forget (nerve I)).mapIso (grothendieckWeightedNerveReplacementIso F))
    (grothendieckWeightedNerveReplacementIso F).hom.w

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
