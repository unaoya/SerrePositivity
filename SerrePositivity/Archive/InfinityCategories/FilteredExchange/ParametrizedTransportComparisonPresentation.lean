module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ParametrizedTransportPullbackFamily
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoCurryPointComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportMapCurryPresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ParametrizedTransportNativeComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ParametrizedTransportPullbackDisplay
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportMapTargetTransport

/-!
概要：元の全区間への直接比較を、同じ実標的証拠への endpointIso へ値まで戻す。
方針：元の curry と全区間制限の表示変更だけを除去し、同じ一点成分を読む。
規約：元の指定比較を保持。使われ方：指定一点区間の比較の実二 prism への回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {E B L : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
  (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
  (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
  (T : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ)
local notation "U" => parametrizedTransportPullbackFamily p γ h₀ h₁
local notation "e" => FiberTransportFamily.endpointIso p (𝟙 _) γ h₁ T U

/-- 元の直接比較は、元の全区間から引き戻した同じ実標的との指定全作用比較。 -/
lemma fiberTransportFamily_parametrized_heq_mapIso :
    HEq (FiberTransportFamily.mapIso_parametrized p γ h₀ h₁ T)
      (FiberTransportFamily.mapIso p (𝟙 _) γ h₁ T U) := by
  have he := fiberTransportFamily_parametrized_heq_native p γ h₀ h₁ T
  have hU := parametrizedTransportPullbackFamily_eq_native p γ h₀ h₁
  exact he.trans (fiberTransportFamily_mapIso_heq_of_target_eq p (𝟙 _) γ h₁ T _ U hU.symm)

/-- 元の直接比較は、同じ実標的との指定 endpointIso の curry。 -/
lemma fiberTransportFamily_parametrized_heq_endpoint_curry :
    HEq (FiberTransportFamily.mapIso_parametrized p γ h₀ h₁ T) (FunctorIso.curry e) :=
  (fiberTransportFamily_parametrized_heq_mapIso p γ h₀ h₁ T).trans
    (heq_of_eq (fiberTransportFamily_mapIso_eq_endpoint_curry p (𝟙 _) γ h₁ T U))

/-- 元の直接比較の一点成分は、同じ実二 prism の endpointIso の同じ係数制限。 -/
lemma fiberTransportFamily_parametrized_app_heq_endpoint [Quasicategory L] (l : L _⦋0⦌) :
    HEq ((FiberTransportFamily.mapIso_parametrized p γ h₀ h₁ T).app l)
      (FunctorIso.precomp e (lift (𝟙 (vertexFiber p a)) (SSet.const l))) := by
  have hm := parametrizedTransportPullbackFamily_map p γ h₀ h₁
  have he := functorIso_app_heq_of_heq
    (FiberTransportFamily.mapIso_parametrized p γ h₀ h₁ T) (FunctorIso.curry e)
    rfl hm.symm (fiberTransportFamily_parametrized_heq_endpoint_curry p γ h₀ h₁ T) l
  exact he.trans (functorIso_curry_app_heq_precomp e l)

end SerrePositivity.InfinityCategories.F2
