module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StrictSimplicialBarRealization
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ClosedMapCoconeInitial
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison

/-!
# 元の直和実現を頂点に持つ指定余錐の余極限性

## 概要
一点評価の同じ鎖ホモトピー同値から、既に指定した bar 余錐の余極限性を得る。

## 方針
一点評価による H⁰ の同値は可逆射を反映する。余錐は再構成しない。

## 規約
全右 dg 加群の nerve での主張であり、一般の擬同型の可逆性は使わない。

## 使われ方
HA 1.2.4。元の実現を頂点とする native 比較の第一段。
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
variable (A : Type u) [CommRing A]

/-- 一点評価の同じ鎖ホモトピー同値を、加群 H⁰ での同じ射の可逆性へ戻す。 -/
theorem ringModuleHom_isIso_onHomotopy_of_point
    {M N : ModuleCategory A PUnit.{1}} (f : M ⟶ N)
    (e : HomotopyEquiv ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M)
      ((moduleEvaluation A PUnit.{1} PUnit.unit).obj N))
    (he : e.hom = (moduleEvaluation A PUnit.{1} PUnit.unit).map f) :
    IsIso ((moduleToHomotopy A PUnit.{1}).map f) := by
  let H := (ringEvaluationHomotopyEquivalence A).functor ⋙ complexHomotopyComparison A
  have h : IsIso (H.map ((moduleToHomotopy A PUnit.{1}).map f)) := by
    change IsIso ((_root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map f))
    rw [← he]
    exact (inferInstance : IsIso (_root_.HomotopyCategory.isoOfHomotopyEquiv e).hom)
  exact isIso_of_reflects_iso _ H

/-- 元の比較閉射は、加群 H⁰ で可逆である。 -/
theorem strictSimplicialBarRealizationHom_isIso_onHomotopy
    (F : SimplicialObject (ModuleCategory A PUnit.{1})) :
    IsIso ((moduleToHomotopy A PUnit.{1}).map (strictSimplicialBarRealizationHom A F)) :=
  ringModuleHom_isIso_onHomotopy_of_point A _
    (strictSimplicialBarRealizationPointHomotopyEquiv A F)
    (strictSimplicialBarRealizationPointHomotopyEquiv_hom A F)

/-- 元の実現を頂点に持つ、同じ指定余錐そのものが余極限である。 -/
theorem strictSimplicialBarRealizationCocone_isColimit
    (F : SimplicialObject (ModuleCategory A PUnit.{1})) :
    IsColimitCone (strictSimplicialBarRealizationCocone A F) :=
  dgCoherentBarClosedMapCocone_isColimit A PUnit.{1} (smallStrictBarDiagram A F) _ _
    (strictSimplicialBarRealizationHom_isIso_onHomotopy A F)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
