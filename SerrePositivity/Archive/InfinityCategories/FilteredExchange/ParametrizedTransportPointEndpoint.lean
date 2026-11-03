module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ParametrizedTransportPullbackFamily
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorCurryPointEvaluation

/-!
概要：全区間普遍輸送の同じ制限証拠の実一点終点を、同じ普遍全作用の一点評価へ戻す。
方針：任意の left fibration 上で同じ全作用と curry の一点評価を計算する。
規約：元の輸送を保持。使われ方：具体的 pointed 射影での型展開を分割する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ全区間制限証拠の実一点終点は、同じ普遍全作用の同じ区間での評価。 -/
lemma parametrizedTransportPullbackFamily_point_endpoint {E B L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b) (l : L _⦋0⦌) :
    lift (𝟙 (vertexFiber p a)) (SSet.const l) ≫
      (parametrizedTransportPullbackFamily p γ h₀ h₁).endpoint =
    (functorVertexEquiv _ _).symm ((parametrizedFiberTransport p a b).app (Opposite.op ⦋0⦌)
      ((intervalMappingCurryOfEndpoints γ h₀ h₁).app (Opposite.op ⦋0⦌) l)) := by
  let U := parametrizedTransportPullbackFamily p γ h₀ h₁
  exact functorCurry_point_evaluation_of_map_eq
    (A := vertexFiber p a) (X := vertexFiber p b) U.endpoint
    (intervalMappingCurryOfEndpoints γ h₀ h₁ ≫ parametrizedFiberTransport p a b)
    (parametrizedTransportPullbackFamily_map p γ h₀ h₁) l

end SerrePositivity.InfinityCategories.F2
