module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismDiagonalVertices
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoEndpointTransport

/-!
概要：元の二実 prism 間の相対同型の両終点像を、同じ実 fiber の指定比較として読む。
方針：全端点評価と全対角終点評価の同じ頂点等式だけで表示を揃える。
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

/-- 元の二実 prism の相対同型の実終点像。初期値は別々に動いてよい。 -/
def relativePrismActualEndpointIso : FunctorIso g g' :=
  vertexIsoOfEq (VertexIso.map e (curry G))
    (relativePrismEvaluationEndpoint_curry_vertex p β W hW 1 b h₁ g he)
    (relativePrismEvaluationEndpoint_curry_vertex p β W' hW' 1 b h₁ g' he')

/-- 同じ相対同型の同じ普遍対角終点像を、元の実初期値で読む。 -/
def relativePrismNativeEndpointIso :
    FunctorIso (diagonalFiberTransport p f (intervalMappingCurryOfEndpoints β h₀ h₁))
      (diagonalFiberTransport p f' (intervalMappingCurryOfEndpoints β h₀ h₁)) :=
  vertexIsoOfEq (VertexIso.map e (curry (diagonalFiberTransport p F c)))
    (relativePrismDiagonalNative_curry_vertex p β a b h₀ h₁ W hW f hs)
    (relativePrismDiagonalNative_curry_vertex p β a b h₀ h₁ W' hW' f' hs')

end SerrePositivity.InfinityCategories.F2
