module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDerivedNaturalComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeRealizationFamily
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ReplacementTotalHomotopy

/-!
概要：元の単体的置換の増大を、strict半自由図式の実現の全族比較として公開する。
方針：既存の自然変換を元の通常複体図式へ制限し、同じ成分の擬同型性を評価する。
規約：元の自然変換と全パラメーターを保持する。正規化barとの比較は別に行う。
使われ方：3b-3 R6、3b-1の増大の全関手同型と元の直和実現の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A]

local instance : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape
local instance : HasCoproducts.{u} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 同じstrict図式の単体的置換を直和実現する、元の通常関手。 -/
def strictSemifreeReplacementRealization :
    StrictSemifreeDiagram A SimplexCategoryᵒᵖ ⥤ Complex A :=
  strictSemifreeUnderlyingComplex A .simplicial ⋙
    simplicialReplacementFunctor (J := SimplexCategoryᵒᵖ) (C := Complex A) ⋙ directSumTotalFunctor A

/-- 元の単体的置換の増大の、元の自然変換への制限。 -/
def strictSemifreeReplacementAugmentation :
    strictSemifreeReplacementRealization A ⟶ strictSemifreeRealizationComplex A :=
  Functor.whiskerLeft (strictSemifreeUnderlyingComplex A .simplicial)
    (replacementTotalAugmentationNatTrans A)

/-- その同じ各増大は、既存の鎖ホモトピー同値の前向きの擬同型。 -/
instance strictSemifreeReplacementAugmentation_quasiIso
    (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    QuasiIso ((strictSemifreeReplacementAugmentation A).app F) :=
  inferInstanceAs (QuasiIso ((replacementTotalAugmentationNatTrans A).app
    ((strictSemifreeUnderlyingComplex A .simplicial).obj F)))

/-- 元の同じ増大による、単体的置換の実現と元の実現との全関手同型。 -/
def strictSemifreeReplacementRealizationIso :
    FunctorIso (nerveMap (strictSemifreeReplacementRealization A) ≫ complexDerivedEvaluation A)
      (strictSemifreeRealizationFamily A) :=
  complexDerivedNatTransIso A (strictSemifreeReplacementAugmentation A) (fun _ => inferInstance)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
