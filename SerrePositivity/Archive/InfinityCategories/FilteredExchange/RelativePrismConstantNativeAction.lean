module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismDiagonalComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalTransportConstantInterval
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismEndpointComparisons
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedRestrictionNaturality

/-!
概要：固定区間上の全相対関手の native 終点作用を、同じ全始点評価へ因数分解する。
方針：全係数の底の区間を厳密に回収し、同じ普遍輸送の一点評価と curry を使う。
規約：元の全係数を保持。使われ方：最後辺の始点移動と native 終点移動の整合。
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
local notation "c" => intervalMappingCurryOfEndpoints γ
  (relativePrismEvaluation_base_endpoint p β 0 a h₀)
  (relativePrismEvaluation_base_endpoint p β 1 b h₁)

omit [LeftFibration p] in
/-- 同じ全相対関手の底の全区間は、元の底の全区間の係数射影による制限。 -/
lemma relativePrismEvaluation_curve :
    c = fst A R ≫ intervalMappingCurryOfEndpoints β h₀ h₁ := by
  apply intervalMappingUncurry_injective
  rw [intervalMappingUncurry_curryOfEndpoints, intervalMappingUncurry_precomp,
    intervalMappingUncurry_curryOfEndpoints]

/-- 固定区間上の全 native 終点作用は、同じ全始点評価への普遍輸送の後合成。 -/
lemma relativePrismNative_curry_constant (v : (intervalMappingSpace a b) _⦋0⦌)
    (hv : intervalMappingCurryOfEndpoints β h₀ h₁ = SSet.const v) :
    curry (diagonalFiberTransport p F c) = curry F ≫ (ihom A).map
      ((functorVertexEquiv _ _).symm
        ((parametrizedFiberTransport p a b).app (Opposite.op ⦋0⦌) v)) := by
  rw [relativePrismEvaluation_curve p β a b h₀ h₁, hv, SSet.comp_const,
    diagonalFiberTransport_constant_interval, curry_natural_right]

/-- 固定区間の native 終点像は、元の同じ相対同型の始点像への同じ輸送の像。 -/
lemma relativePrismNativeEndpointIso_constant_heq
    (v : (intervalMappingSpace a b) _⦋0⦌)
    (hv : intervalMappingCurryOfEndpoints β h₀ h₁ = SSet.const v)
    (W W' : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
    (f f' : A ⟶ vertexFiber p a)
    (hs : prismEndpoint 0 A ≫ W = f ≫ vertexFiberι p a)
    (hs' : prismEndpoint 0 A ≫ W' = f' ≫ vertexFiberι p a)
    (e : VertexIso (relativeFunctorVertex p β W hW)
      (relativeFunctorVertex p β W' hW')) :
    HEq (relativePrismNativeEndpointIso p β a b h₀ h₁ W W' hW hW' f f' hs hs' e)
      (VertexIso.map (VertexIso.map e (curry F)) ((ihom A).map
        ((functorVertexEquiv _ _).symm
          ((parametrizedFiberTransport p a b).app (Opposite.op ⦋0⦌) v)))) := by
  unfold relativePrismNativeEndpointIso
  refine (vertexIsoOfEq_heq _ _ _).trans ?_
  exact (vertexIso_map_heq e (relativePrismNative_curry_constant p β a b h₀ h₁ v hv)).trans
    (heq_of_eq (vertexIso_map_comp e _ _).symm)

end SerrePositivity.InfinityCategories.F2
