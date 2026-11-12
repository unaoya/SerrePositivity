module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.SliceEvaluationHomotopy
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.HomotopyPostcompositionEvaluation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyNatTransPrecomposition

/-!
概要：関手圏の普遍 slice 評価の成分を元の実錐へ移し、恒等錐成分を恒等射に同定する。
方針：同じ後合成ホモトピーの評価と、全時刻で固定された恒等錐を照合する。
規約：パラメータは任意。使われ方：選んだ終対象錐の値と実 pinched Hom 族との比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof
/-- 全パラメータの slice 評価の成分は、元の普遍錐の同じ実関手への制限。 -/
lemma roofFunctorSliceEvaluation_component_arrow (K : SSet.{u}) {X : SSet.{u}}
    (z : X _⦋0⦌) (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h₁).app
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy
          z) a))) := by
  have h₀ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyNatTransOfEndpoints_app_arrow
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h₁
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  have h₁ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyNatTransOfEndpoints_app_arrow
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.homotopyPostcomposition K (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z)).h
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.homotopyPostcomposition K (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z)).h₀
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.homotopyPostcomposition K (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z)).h₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  exact h₀.trans (h₁.symm.trans
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.homotopyPostcomposition_component_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z) a))
/-- 恒等錐の任意定数族上でも、普遍評価の全時刻は同じ頂点に厳密に定値。 -/
lemma roofSliceEvaluationHomotopy_const_identity_h (K : SSet.{u}) {X : SSet.{u}} (z : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z)
      (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone z))).h = SSet.const z := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.const_point_comp_yoneda (A := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone z)).symm
  change ((SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone z)) ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z).h = _
  rw [hc, MonoidalCategory.comp_whiskerRight, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_identity, SSet.comp_const, SSet.comp_const]
/-- 恒等錐の定数族上の普遍評価成分は、同じ定値関手の恒等射。 -/
lemma roofFunctorSliceEvaluation_identity_component_arrow (K : SSet.{u}) {X : SSet.{u}}
    (z : X _⦋0⦌) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h₁).app
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity K z))) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := K) z)))) := by
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := K) z)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z) (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone z)))
  have he : e.edge = (Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj X)) v).edge := by
    change SSet.yonedaEquiv (curry (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z) (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone z))).h) = _
    rw [roofSliceEvaluationHomotopy_const_identity_h]
    have hc : curry (SSet.const z : K ⊗ (Δ[1] : SSet.{u}) ⟶ X) =
        (SSet.const v : (Δ[1] : SSet.{u}) ⟶ (ihom K).obj X) := by
      apply uncurry_injective
      rw [uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex, SSet.comp_const]
    rw [hc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one v
  exact (roofFunctorSliceEvaluation_component_arrow K z
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone z))).trans
      ((Truncated.HomotopyCategory.congr_arrowMk_homMk e (Truncated.Edge.id v) he).trans
        (congrArg Arrow.mk (Truncated.HomotopyCategory.homMk_id
          (V := (truncation 2).obj ((ihom K).obj X)) v)))
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof
