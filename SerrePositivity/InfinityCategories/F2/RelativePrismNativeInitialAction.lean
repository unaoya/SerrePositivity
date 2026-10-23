module

public import SerrePositivity.InfinityCategories.F2.RelativePrismEndpointComparisons
public import SerrePositivity.InfinityCategories.F2.RelativePrismConstantNativeAction
public import SerrePositivity.InfinityCategories.F2.DiagonalFiberFamilyCurry

/-!
概要：同じ相対同型の native 終点像を、全始点評価の指定像への作用に因数分解する。
方針：元の全底区間を係数射影で回収し、同じ全区間族の関手空間の作用を使う。
規約：全区間族を保持。使われ方：零面比較の指定中間像から native 像への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B A : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (β : (Δ[1] : SSet.{u}) ⊗ A ⟶ B) (a b : B _⦋0⦌)
  (h₀ : prismEndpoint 0 A ≫ β = SSet.const a)
  (h₁ : prismEndpoint 1 A ≫ β = SSet.const b)
local notation "R" => relativeFunctorSpace p β
local notation "γ" => (Δ[1] ◁ fst A R) ≫ β
local notation "F" => relativePrismEvaluationEndpoint p β 0 a h₀
local notation "c" => intervalMappingCurryOfEndpoints β h₀ h₁
local notation "C" => intervalMappingCurryOfEndpoints γ
  (relativePrismEvaluation_base_endpoint p β 0 a h₀)
  (relativePrismEvaluation_base_endpoint p β 1 b h₁)
local notation "Ω" => functorPairRight c ≫
  CategoryTheory.Functor.map (ihom A)
    (FiberTransportFamily.endpoint (parametrizedFiberTransportFamily p a b))

/-- 全 native 終点評価は、同じ全始点評価と元の同じ全区間族の作用の合成。 -/
lemma relativePrismNative_curry_eq_initial_action :
    curry (diagonalFiberTransport p F C) = curry F ≫ Ω := by
  rw [relativePrismEvaluation_curve p β a b h₀ h₁,
    diagonalFiberTransport_family_curry, Category.assoc]

/-- 元の native 指定像は、同じ始点評価の指定像への同じ全区間族の作用。 -/
lemma relativePrismNativeEndpointIso_heq_initial_action
    (W W' : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
    (f f' : A ⟶ vertexFiber p a)
    (hs : prismEndpoint 0 A ≫ W = f ≫ vertexFiberι p a)
    (hs' : prismEndpoint 0 A ≫ W' = f' ≫ vertexFiberι p a)
    (e : VertexIso (relativeFunctorVertex p β W hW) (relativeFunctorVertex p β W' hW')) :
    HEq (relativePrismNativeEndpointIso p β a b h₀ h₁ W W' hW hW' f f' hs hs' e)
      (VertexIso.map (VertexIso.map e (curry F)) Ω) := by
  unfold relativePrismNativeEndpointIso
  refine (vertexIsoOfEq_heq _ _ _).trans ?_
  exact (vertexIso_map_heq e (relativePrismNative_curry_eq_initial_action p β a b h₀ h₁)).trans
    (heq_of_eq (vertexIso_map_comp e _ _).symm)

end SerrePositivity.InfinityCategories.F2
