module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismEndpointComparisons
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismDiagonalComponent

/-!
概要：始点も動く元の二実 prism の指定対角比較は、同じ相対同型の両端像に自然。
方針：全相対関手上の自然性の四頂点と四指定成分を、元の同じ実表示へ戻す。
規約：元の相対同型を保持。使われ方：全三角形の最後辺で始点も動く比較の整合。
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
  (W W' : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
  (f f' : A ⟶ vertexFiber p a) (g g' : A ⟶ vertexFiber p b)
  (hs : prismEndpoint 0 A ≫ W = f ≫ vertexFiberι p a)
  (hs' : prismEndpoint 0 A ≫ W' = f' ≫ vertexFiberι p a)
  (he : prismEndpoint 1 A ≫ W = g ≫ vertexFiberι p b)
  (he' : prismEndpoint 1 A ≫ W' = g' ≫ vertexFiberι p b)
  (e : VertexIso (relativeFunctorVertex p β W hW) (relativeFunctorVertex p β W' hW'))
local notation "R" => relativeFunctorSpace p β
local notation "γ" => (Δ[1] ◁ fst A R) ≫ β
local notation "F" => relativePrismEvaluationEndpoint p β 0 a h₀
local notation "G" => relativePrismEvaluationEndpoint p β 1 b h₁
local notation "c" => intervalMappingCurryOfEndpoints γ
  (relativePrismEvaluation_base_endpoint p β 0 a h₀)
  (relativePrismEvaluation_base_endpoint p β 1 b h₁)

local notation "v" => relativeFunctorVertex p β W hW
local notation "v'" => relativeFunctorVertex p β W' hW'
local notation "Θ" => relativePrismDiagonalComparisonCurry p β a b h₀ h₁
local notation "Aiso" => relativePrismActualEndpointIso p β b h₁ W W' hW hW' g g' he he' e
local notation "Niso" => relativePrismNativeEndpointIso p β a b h₀ h₁ W W' hW hW' f f' hs hs' e
local notation "D" => leftFibrationPrism_diagonalTransportIso p f g β h₀ h₁ W hs he hW
local notation "D'" => leftFibrationPrism_diagonalTransportIso p f' g' β h₀ h₁ W' hs' he' hW'

/-- 始点も動く二実 prism の元の指定比較は、両端の同じ相対同型の像と厳密に自然。 -/
lemma relativePrismSpecified_naturality : Aiso ≪≫ D' = D ≪≫ Niso := by
  exact vertexIso_square_of_heq (VertexIso.map e (curry G)) (FunctorIso.app Θ v')
    (FunctorIso.app Θ v) (VertexIso.map e (curry (diagonalFiberTransport p F c)))
    Aiso D' D Niso
    (relativePrismEvaluationEndpoint_curry_vertex p β W hW 1 b h₁ g he)
    (relativePrismEvaluationEndpoint_curry_vertex p β W' hW' 1 b h₁ g' he')
    (relativePrismDiagonalNative_curry_vertex p β a b h₀ h₁ W hW f hs)
    (relativePrismDiagonalNative_curry_vertex p β a b h₀ h₁ W' hW' f' hs')
    (vertexIsoOfEq_heq _ _ _).symm
    (relativePrismDiagonalComparison_at_vertex p β a b h₀ h₁ W' hW' f' g' hs' he')
    (relativePrismDiagonalComparison_at_vertex p β a b h₀ h₁ W hW f g hs he)
    (vertexIsoOfEq_heq _ _ _).symm
    (relativePrismDiagonalComparison_naturality p β a b h₀ h₁ e)

end SerrePositivity.InfinityCategories.F2
