module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanCoefficientComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ClassificationTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativeNerveStraighteningComparison

/-!
概要：元のGrothendieck–Kan比較を底全体の分類の関手同型へ送る。
方針：指定単位を固定する一つの比較射を選び、既存の同じ底上の分類の移送を適用する。
規約：一点ごとの同型から全図式の同型を推論しない。
使われ方：IS-W2 R03dの両変数の比較の組み立て。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
local instance kanCoefficients (i : I) :
    KanComplex ((grothendieckKanCoefficients F).obj i) := by
  change KanComplex (exInfinity.obj (nerve (F.obj i)))
  infer_instance

/-- 元の単位を固定する、底全体で選んだ一つの比較射。 -/
def grothendieckKanCoefficientComparison :
    ((continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (nerveMap (Grothendieck.forget F)))).left ⟶
        weightedNerve (grothendieckKanCoefficients F) :=
  (exists_grothendieckKanCoefficientComparison F).choose

/-- 同じ比較射は元の射影を保つ。 -/
theorem grothendieckKanCoefficientComparison_projection :
    grothendieckKanCoefficientComparison F ≫
      weightedNerveProjection (grothendieckKanCoefficients F) =
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom :=
  (exists_grothendieckKanCoefficientComparison F).choose_spec.1

/-- 同じ比較射は元の置換単位に沿って元の比較射を延長する。 -/
theorem grothendieckKanCoefficientComparison_unit :
    ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (Grothendieck.forget F)))).left ≫
        grothendieckKanCoefficientComparison F = grothendieckKanCoefficientMap F :=
  (exists_grothendieckKanCoefficientComparison F).choose_spec.2.1

/-- 選んだ同じ比較射自身が前合成同値である。 -/
theorem grothendieckKanCoefficientComparison_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (grothendieckKanCoefficientComparison F) :=
  (exists_grothendieckKanCoefficientComparison F).choose_spec.2.2

/-- 元の全分類とKan係数のweighted nerveの全分類を同じ底上で比較する。 -/
def grothendieckKanReplacementClassificationIso :
    FunctorIso
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom)
      (leftStraighteningInfinityDiagram
        (weightedNerveProjection (grothendieckKanCoefficients F))) := by
  exact leftClassification_of_precompositionEquivalence
    ((continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (nerveMap (Grothendieck.forget F)))).hom
    (weightedNerveProjection (grothendieckKanCoefficients F))
    (grothendieckKanCoefficientComparison F) (grothendieckKanCoefficientComparison_projection F)
    (grothendieckKanCoefficientComparison_isPrecompositionEquivalence F)
/-- 元のEx∞係数を、同じ対象と同じ射のKan値図式として記録する。 -/
def grothendieckKanCoefficientDiagram : I ⥤ KanObject.{u} where
  obj i := ⟨(grothendieckKanCoefficients F).obj i, inferInstance⟩
  map f := (grothendieckKanCoefficients F).map f
  map_id i := (grothendieckKanCoefficients F).map_id i
  map_comp f g := (grothendieckKanCoefficients F).map_comp f g

/-- 同じKan係数の全図式を、元のGrothendieck置換のnative全分類へつなぐ。 -/
def grothendieckKanNativeClassificationUnitIso :
    FunctorIso (kanDiagramCoherentNerve (grothendieckKanCoefficientDiagram F))
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom) :=
  (weightedNerveNativeStraighteningUnitIso (grothendieckKanCoefficientDiagram F)).trans
    (grothendieckKanReplacementClassificationIso F).symm
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
