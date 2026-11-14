module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsGrothendieck
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanClassification
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationEquivalenceMap
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence

/-!
概要：同じ全要素圏の元の置換を、同じ全Grothendieck係数のnative分類へつなぐ。
方針：同じ底への圏同値のnerveを元の置換へ送り、その全分類を移送する。
規約：底と元の置換単位を保ち、固定始域のroofとの等式は別に確認する。
使われ方：全source frameの要素圏から両変数のnative Homへの接続。
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
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

/-- 同じ元の全要素圏からGrothendieck表示への底上のnerveの射。 -/
def simplicialElementsGrothendieckOverMap :
    Over.mk (nerveMap (simplicialTotalElementsProjection F)) ⟶
      Over.mk (nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F))) :=
  Over.homMk (nerveMap (simplicialElementsGrothendieckInverse F)) (by
    change nerveMap (simplicialElementsGrothendieckInverse F ⋙
      Grothendieck.forget (simplicialElementsCatDiagram F)) = _
    rw [simplicialElementsGrothendieckInverse_projection]
    rfl)

/-- 同じ底上のnerveの射そのものは前合成同値。 -/
theorem simplicialElementsGrothendieckOverMap_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (simplicialElementsGrothendieckOverMap F).left :=
  (SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveQCatEquivalence
    (simplicialElementsGrothendieckEquivalence F).symm).isQCatEquivalence.isPrecompositionEquivalence

/-- 元の二つの置換の全空間の同じ比較射。 -/
def simplicialElementsGrothendieckReplacementMap :=
  (continuousLeftFibrationReplacement (nerve I)).map (simplicialElementsGrothendieckOverMap F)

/-- 同じ置換の比較は元の単位の自然性の正方形を保つ。 -/
theorem simplicialElementsGrothendieckReplacementMap_unit :
    ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).left ≫
        (simplicialElementsGrothendieckReplacementMap F).left =
      (simplicialElementsGrothendieckOverMap F).left ≫
        ((continuousLeftFibrationReplacementUnit (nerve I)).app
          (Over.mk (nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F))))).left :=
  (congrArg (fun f => f.left) ((continuousLeftFibrationReplacementUnit (nerve I)).naturality
    (simplicialElementsGrothendieckOverMap F))).symm

/-- 同じ元の置換の比較射そのものが前合成同値。 -/
theorem simplicialElementsGrothendieckReplacementMap_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (simplicialElementsGrothendieckReplacementMap F).left := by
  have : Quasicategory
      (Over.mk (nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F)))).left := by
    change Quasicategory (nerve (Grothendieck (simplicialElementsCatDiagram F)))
    infer_instance
  exact continuousLeftFibrationReplacement_map_isPrecompositionEquivalence _
    (simplicialElementsGrothendieckOverMap_isPrecompositionEquivalence F)

/-- 同じ全要素圏の元の置換とGrothendieck表示の元の置換の全分類の同型。 -/
def simplicialElementsGrothendieckReplacementClassificationIso :
    FunctorIso
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).hom)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F))))).hom) :=
  leftClassification_of_precompositionEquivalence _ _
    (simplicialElementsGrothendieckReplacementMap F).left
    (simplicialElementsGrothendieckReplacementMap F).w
    (simplicialElementsGrothendieckReplacementMap_isPrecompositionEquivalence F)

/-- 同じ全要素係数のKan図式と元の全要素圏のnativeな全分類の同型。 -/
def simplicialElementsNativeClassificationUnitIso :
    FunctorIso
      (kanDiagramCoherentNerve (grothendieckKanCoefficientDiagram (simplicialElementsCatDiagram F)))
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).hom) :=
  (grothendieckKanNativeClassificationUnitIso (simplicialElementsCatDiagram F)).trans
    (simplicialElementsGrothendieckReplacementClassificationIso F).symm
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
