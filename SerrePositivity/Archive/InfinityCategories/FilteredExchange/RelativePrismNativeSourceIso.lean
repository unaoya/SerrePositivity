module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismNativeInitialAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismInitialEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalFiberSourceIsoAction

/-!
概要：元の相対比較の native 終点像は、指定始点像の元の sourceIso に一致する。
方針：両者を同じ全区間の関手空間作用による指定像へ戻す。
規約：元の指定比較と全係数を保持。使われ方：持ち上げ四角形の上辺比較の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B A : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (β : (Δ[1] : SSet.{u}) ⊗ A ⟶ B) (a b : B _⦋0⦌)
  (h₀ : prismEndpoint 0 A ≫ β = SSet.const a)
  (h₁ : prismEndpoint 1 A ≫ β = SSet.const b)
  (W W' : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
  (f f' : A ⟶ vertexFiber p a)
  (hs : prismEndpoint 0 A ≫ W = f ≫ vertexFiberι p a)
  (hs' : prismEndpoint 0 A ≫ W' = f' ≫ vertexFiberι p a)
  (e : VertexIso (relativeFunctorVertex p β W hW) (relativeFunctorVertex p β W' hW'))

/-- 元の native 終点像は、元の指定始点像の同じ sourceIso そのもの。 -/
lemma relativePrismNativeEndpointIso_heq_sourceIso :
    HEq (relativePrismNativeEndpointIso p β a b h₀ h₁ W W' hW hW' f f' hs hs' e)
      (diagonalFiberTransport_sourceIso p
        (relativePrismInitialEndpointIso p β a h₀ W W' hW hW' f f' hs hs' e)
        (intervalMappingCurryOfEndpoints β h₀ h₁)) := by
  have hn := relativePrismNativeEndpointIso_heq_initial_action p β a b h₀ h₁
    W W' hW hW' f f' hs hs' e
  let Ω := functorPairRight (intervalMappingCurryOfEndpoints β h₀ h₁) ≫
    (ihom A).map (parametrizedFiberTransportFamily p a b).endpoint
  have hm := vertexIsoOfEq_map_heq
    (VertexIso.map e (curry (relativePrismEvaluationEndpoint p β 0 a h₀)))
    (relativePrismEvaluationEndpoint_curry_vertex p β W hW 0 a h₀ f hs)
    (relativePrismEvaluationEndpoint_curry_vertex p β W' hW' 0 a h₀ f' hs') Ω
  exact hn.trans (hm.symm.trans
    (diagonalFiberTransport_sourceIso_heq_action p
      (relativePrismInitialEndpointIso p β a h₀ W W' hW hW' f f' hs hs' e)
      (intervalMappingCurryOfEndpoints β h₀ h₁)).symm)

end SerrePositivity.InfinityCategories.F2
