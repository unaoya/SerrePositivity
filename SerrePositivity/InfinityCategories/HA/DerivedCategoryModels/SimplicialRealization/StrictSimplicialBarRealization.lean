module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarNormalizedComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ReplacementTotalHomotopy
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ClosedMapCocone

/-!
# 厳密な単体的図式の元の実現を頂点に持つ指定 bar 余錐

## 概要
同じ正規化 bar 比較と元の増大を合成し、元の直和全複体への指定閉射を作る。

## 方針
一点評価の充満忠実性で同じ増大を加群射へ戻し、既存の Hom 空間同型で余錐へ送る。

## 規約
正規化比較も増大も、その前向きの射を保つ。

## 使われ方
HA 1.2.4、HTT 4.2.4.1。計算した頂点・脚・高次成分を持つ native 比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite AlgebraicTopology HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable (A : Type u) [CommRing A]

/-- 元の単体的図式の同じ直和全複体を一点加群とした標的。 -/
def strictSimplicialRealizationModule (F : SimplicialObject (ModuleCategory A PUnit.{1})) :
    RightModule A PUnit.{1} :=
  ringModule A ((directSumTotalFunctor A).obj (smallStrictBarCoefficientDiagram A F))

/-- 同じ全複体増大を、厳密な一点加群射へ戻す。 -/
def strictSimplicialBarAugmentation (F : SimplicialObject (ModuleCategory A PUnit.{1})) :
    ForgetEnrichment.of (Complex A) (smallStrictBarTotalTarget A F) ⟶
      ForgetEnrichment.of (Complex A) (strictSimplicialRealizationModule A F) :=
  (ringEvaluationHomEquiv A _ _).symm
    (replacementAugmentationTotalHomotopyEquiv A (smallStrictBarCoefficientDiagram A F)).hom

/-- この加群増大の一点評価は、元の同じ増大である。 -/
theorem strictSimplicialBarAugmentation_point (F : SimplicialObject (ModuleCategory A PUnit.{1})) :
    (moduleEvaluation A PUnit.{1} PUnit.unit).map (strictSimplicialBarAugmentation A F) =
      (replacementAugmentationTotalHomotopyEquiv A (smallStrictBarCoefficientDiagram A F)).hom :=
  (ringEvaluationHomEquiv A _ _).apply_symm_apply _

/-- 既存正規化 bar から元の実現への、同じ二比較の合成。 -/
def strictSimplicialBarRealizationHom (F : SimplicialObject (ModuleCategory A PUnit.{1})) :
    ForgetEnrichment.of (Complex A)
      (dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)) ⟶
    ForgetEnrichment.of (Complex A) (strictSimplicialRealizationModule A F) :=
  smallStrictBarNormalizedTotalHom A F ≫ strictSimplicialBarAugmentation A F

/-- この同じ比較の一点評価を前向きの射とする鎖ホモトピー同値。 -/
def strictSimplicialBarRealizationPointHomotopyEquiv
    (F : SimplicialObject (ModuleCategory A PUnit.{1})) :
    HomotopyEquiv
      ((dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)).obj
        (op PUnit.unit)) ((strictSimplicialRealizationModule A F).obj (op PUnit.unit)) :=
  (smallStrictBarNormalizedTotalPointHomotopyEquiv A F).trans
    (replacementAugmentationTotalHomotopyEquiv A (smallStrictBarCoefficientDiagram A F))

/-- 合成した鎖ホモトピー同値も同じ厳密な比較射を持つ。 -/
theorem strictSimplicialBarRealizationPointHomotopyEquiv_hom
    (F : SimplicialObject (ModuleCategory A PUnit.{1})) :
    (strictSimplicialBarRealizationPointHomotopyEquiv A F).hom =
      (moduleEvaluation A PUnit.{1} PUnit.unit).map (strictSimplicialBarRealizationHom A F) := by
  change (smallStrictBarNormalizedTotalPointHomotopyEquiv A F).hom ≫
    (replacementAugmentationTotalHomotopyEquiv A (smallStrictBarCoefficientDiagram A F)).hom = _
  rw [smallStrictBarNormalizedTotalPointHomotopyEquiv_hom,
    ← strictSimplicialBarAugmentation_point, ← CategoryTheory.Functor.map_comp]
  rfl

/-- 元の実現を頂点に指定し、同じ比較閉射を全高次成分まで持つ実際の余錐。 -/
def strictSimplicialBarRealizationCocone (F : SimplicialObject (ModuleCategory A PUnit.{1})) :
    JoinCocone (smallStrictBarDiagram A F) :=
  dgCoherentBarClosedMapCocone A PUnit.{1} (smallStrictBarDiagram A F)
    (strictSimplicialRealizationModule A F) (strictSimplicialBarRealizationHom A F)

/-- 指定した余錐の頂点は、元の同じ実現加群の頂点である。 -/
theorem strictSimplicialBarRealizationCocone_vertex
    (F : SimplicialObject (ModuleCategory A PUnit.{1})) :
    (strictSimplicialBarRealizationCocone A F).vertex =
      Simplex.vertex (strictSimplicialRealizationModule A F) :=
  dgCoherentBarClosedMapCocone_vertex A PUnit.{1} (smallStrictBarDiagram A F) _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
