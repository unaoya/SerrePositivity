module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramValueSectionsComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.NerveProductSwapIso

/-!
概要：元の添字のtwisted-arrow射影を使い、frame係数のcoherent endを固定する。
方針：反対圏のnerveと積の既存同型で、同じ始点・終点を二変数係数へ送る。
規約：frame Homからこのendへの同値は、このファイルでは主張しない。
使われ方：HTT 4.2.4.4のRR02で比較する導来endの係数。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 積の同型で入れ替えた添字を、元の始点・終点の順へ戻す通常の関手。 -/
def strictDiagramEndIndexFunctor (d : StrictDiagramDirection) :
    AsSmall.{u} (strictDiagramIndex d) × (AsSmall.{u} (strictDiagramIndex d))ᵒᵖ ⥤
      AsSmall.{u} ((strictDiagramIndex d)ᵒᵖ × strictDiagramIndex d) :=
  CategoryTheory.Prod.swap _ _ ⋙
    (AsSmall.down : AsSmall.{u} (strictDiagramIndex d) ⥤ strictDiagramIndex d).op.prod
      (AsSmall.down : AsSmall.{u} (strictDiagramIndex d) ⥤ strictDiagramIndex d) ⋙ AsSmall.up

/-- 元の添字のtwisted arrowの始点・終点を、同じ二変数係数の底へ送る。 -/
def strictDiagramEndIndexMap (d : StrictDiagramDirection) :
    TwistedArrow (nerve (AsSmall.{u} (strictDiagramIndex d))) ⟶
      nerve (AsSmall.{u} ((strictDiagramIndex d)ᵒᵖ × strictDiagramIndex d)) :=
  twistedArrowProjection (nerve (AsSmall.{u} (strictDiagramIndex d))) ≫
    ((nerveOppositeIso (C := AsSmall.{u} (strictDiagramIndex d))).hom ⊗ₘ
      𝟙 (nerve (AsSmall.{u} (strictDiagramIndex d)))) ≫
    (nerveProductSwapIso (AsSmall.{u} (strictDiagramIndex d))
      (AsSmall.{u} (strictDiagramIndex d))ᵒᵖ).inv ≫ nerveMap (strictDiagramEndIndexFunctor d)

variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
  (X Y : StrictComplexDiagram A d)

/-- 同じ評価frame係数の、twisted-arrowの底上のcoherent end。 -/
def strictDiagramEvaluatedFrameEnd : SSet.{u} :=
  simplicialSections (smallLeftUnstraighteningProjection
    (strictDiagramEvaluatedValueCoefficient A d X Y (strictDiagramEndIndexMap d)))

/-- 標準frame係数の、同じ底上のcoherent end。 -/
def strictDiagramStandardFrameEnd : SSet.{u} :=
  simplicialSections (smallLeftUnstraighteningProjection
    (strictDiagramStandardValueCoefficient A d X Y (strictDiagramEndIndexMap d)))

/-- 同じ係数比較を、この指定したtwisted-arrowの底で使う。 -/
def strictDiagramFrameEndCoefficientComparison :
    strictDiagramEvaluatedFrameEnd A d X Y ⟶ strictDiagramStandardFrameEnd A d X Y :=
  strictDiagramValueSectionsComparison A d X Y (strictDiagramEndIndexMap d)

/-- この指定した係数比較は、同じ切断の射としてホモトピー同値。 -/
lemma strictDiagramFrameEndCoefficientComparison_equivalence :
    IsSimplicialHomotopyEquivalence (strictDiagramFrameEndCoefficientComparison A d X Y) :=
  strictDiagramValueSectionsComparison_equivalence A d X Y (strictDiagramEndIndexMap d)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
