module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightOppositeCoefficientsNaturality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.StrictKanPointedComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCosliceBaseNaturality

/-!
概要：元の elementsComparisonNatural の pointed 成分を、元の左 coslice 比較で表示する。
方針：小さい全空間の縮小同型と strict Kan 比較の既存の第一射影の公式を使う。
規約：比較射と同型の選択を変更しない。
使われ方：G8 の四角形①で、元の比較を区間上の一つの pointed 族に結ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I]

/-- 元の要素の圏の比較の、宇宙を戻した全空間からの pointed 成分。 -/
def setWeightElementsPointed (X : I ⥤ Type u) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve X.Elements) ⟶ PointedSpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (SetWeight.elementsComparisonNatural X) ≫
    (smallLeftUnstraighteningIso (spaceDiagram X)).hom ≫
      pullback.fst pointedSpaceProjection (spaceDiagram X)

/-- 元の比較の pointed 成分は、同じ係数同型と左 coslice の実際の比較で計算できる。 -/
lemma setWeightElementsPointed_formula (X : I ⥤ Type u) :
    setWeightElementsPointed X =
      (SSet.uliftFunctor.{u + 1, u}).map
        (elementsToReplacement X ≫ tautScaffold (coefficients X) ≫
          (SetWeight.coefficientsOppositeWeightedIso X).hom ≫
            (directPointHomWeightedIso (X ⋙ setsToKan)).inv) ≫
        weightedCosliceComparison (X ⋙ setsToKan) pointKanObject ≫
          strictKanPointedApexIso.hom := by
  simp only [setWeightElementsPointed, SetWeight.elementsComparisonNatural, Functor.map_comp,
    Category.assoc, smallReversedWeightedKanUnstraighteningComparison]
  rw [← Category.assoc _ (smallLeftUnstraighteningIso (spaceDiagram X)).hom,
    smallLeftUnstraighteningLift_naturality]
  simp only [reversedWeightedKanUnstraighteningComparison, Category.assoc,
    strictKanUnstraighteningComparison_pointed, Functor.map_comp]

/-- 元の pointed 比較は、添字を通常の関手で制限しても全写像として可換である。 -/
lemma setWeightElementsPointed_base {J : Type u} [SmallCategory J]
    (H : J ⥤ I) (X : I ⥤ Type u) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.precomp H X)) ≫
      setWeightElementsPointed X = setWeightElementsPointed (H ⋙ X) := by
  rw [setWeightElementsPointed_formula, setWeightElementsPointed_formula]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
