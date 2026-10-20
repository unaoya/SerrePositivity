module
public import SerrePositivity.InfinityCategories.Derived.SliceEvaluationHomotopy
public import SerrePositivity.InfinityCategories.Derived.HomotopyPostcompositionEvaluation
public import SerrePositivity.InfinityCategories.Stable.HomotopyNatTransPrecomposition

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
namespace SerrePositivity.InfinityCategories
/-- 全パラメータの slice 評価の成分は、元の普遍錐の同じ実関手への制限。 -/
lemma roofFunctorSliceEvaluation_component_arrow (K : SSet.{u}) {X : SSet.{u}}
    (z : X _⦋0⦌) (a : K ⟶ sliceOver (SSet.yonedaEquiv.symm z)) :
    Arrow.mk ((homotopyNatTransOfEndpoints (roofFunctorSliceEvaluationHomotopy K z).h
      (roofFunctorSliceEvaluationHomotopy K z).h₀ (roofFunctorSliceEvaluationHomotopy K z).h₁).app
        (SSet.HomotopyCategory.mk (functorVertex a))) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp (roofSliceEvaluationHomotopy
          z) a))) := by
  have h₀ := homotopyNatTransOfEndpoints_app_arrow
    (roofFunctorSliceEvaluationHomotopy K z).h
    (roofFunctorSliceEvaluationHomotopy K z).h₀ (roofFunctorSliceEvaluationHomotopy K z).h₁
    (functorVertex a)
  have h₁ := homotopyNatTransOfEndpoints_app_arrow
    (homotopyPostcomposition K (roofSliceEvaluationHomotopy z)).h
    (homotopyPostcomposition K (roofSliceEvaluationHomotopy z)).h₀
    (homotopyPostcomposition K (roofSliceEvaluationHomotopy z)).h₁ (functorVertex a)
  exact h₀.trans (h₁.symm.trans
    (homotopyPostcomposition_component_arrow (roofSliceEvaluationHomotopy z) a))
/-- 恒等錐の任意定数族上でも、普遍評価の全時刻は同じ頂点に厳密に定値。 -/
lemma roofSliceEvaluationHomotopy_const_identity_h (K : SSet.{u}) {X : SSet.{u}} (z : X _⦋0⦌) :
    (functorHomotopyPrecomp (roofSliceEvaluationHomotopy z)
      (SSet.const (X := K) (sliceIdentityCone z))).h = SSet.const z := by
  have hc := (const_point_comp_yoneda (A := K) (sliceIdentityCone z)).symm
  change ((SSet.const (X := K) (sliceIdentityCone z)) ▷ (Δ[1] : SSet.{u})) ≫
    (roofSliceEvaluationHomotopy z).h = _
  rw [hc, MonoidalCategory.comp_whiskerRight, Category.assoc,
    roofSliceEvaluationHomotopy_identity, SSet.comp_const, SSet.comp_const]
/-- 恒等錐の定数族上の普遍評価成分は、同じ定値関手の恒等射。 -/
lemma roofFunctorSliceEvaluation_identity_component_arrow (K : SSet.{u}) {X : SSet.{u}}
    (z : X _⦋0⦌) :
    Arrow.mk ((homotopyNatTransOfEndpoints (roofFunctorSliceEvaluationHomotopy K z).h
      (roofFunctorSliceEvaluationHomotopy K z).h₀ (roofFunctorSliceEvaluationHomotopy K z).h₁).app
        (SSet.HomotopyCategory.mk (roofFunctorSliceIdentity K z))) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk (functorVertex (SSet.const (X := K) z)))) := by
  let v := functorVertex (SSet.const (X := K) z)
  let e := functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp
    (roofSliceEvaluationHomotopy z) (SSet.const (X := K) (sliceIdentityCone z)))
  have he : e.edge = (Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj X)) v).edge := by
    change SSet.yonedaEquiv (curry (functorHomotopyPrecomp
      (roofSliceEvaluationHomotopy z) (SSet.const (X := K) (sliceIdentityCone z))).h) = _
    rw [roofSliceEvaluationHomotopy_const_identity_h]
    have hc : curry (SSet.const z : K ⊗ (Δ[1] : SSet.{u}) ⟶ X) =
        (SSet.const v : (Δ[1] : SSet.{u}) ⟶ (ihom K).obj X) := by
      apply uncurry_injective
      rw [uncurry_curry, uncurry_const_functorVertex, SSet.comp_const]
    rw [hc]
    exact pinchedConstant_one v
  exact (roofFunctorSliceEvaluation_component_arrow K z
    (SSet.const (sliceIdentityCone z))).trans
      ((Truncated.HomotopyCategory.congr_arrowMk_homMk e (Truncated.Edge.id v) he).trans
        (congrArg Arrow.mk (Truncated.HomotopyCategory.homMk_id
          (V := (truncation 2).obj ((ihom K).obj X)) v)))
end SerrePositivity.InfinityCategories
