module

public import SerrePositivity.InfinityCategories.F2.RelativePrismEndpointPrecomposition
public import SerrePositivity.InfinityCategories.F2.RelativePrismEndpointComparisons

/-!
概要：底と二実 prism の明示的な等式で表示を揃えても、指定端点像の値を保持する。
方針：実データの等式を先に消去し、その後で同じ相対頂点同型の値を比較する。
規約：HEq から底・端点の等式を取り出さない。使われ方：実最後辺の両端像の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 底・二実 prism の同じ等式と指定比較の値は、同じ両端評価の指定像を保持する。 -/
lemma relativePrismEndpointImage_heq_of_dataEq {E B A : SSet.{u}}
    (p : E ⟶ B) (β β' : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (W₀ W₁ W₀' W₁' : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (h₀ : W₀ ≫ p = β) (h₁ : W₁ ≫ p = β)
    (h₀' : W₀' ≫ p = β') (h₁' : W₁' ≫ p = β')
    (e : VertexIso (relativeFunctorVertex p β W₀ h₀) (relativeFunctorVertex p β W₁ h₁))
    (e' : VertexIso (relativeFunctorVertex p β' W₀' h₀') (relativeFunctorVertex p β' W₁' h₁'))
    (i : Fin 2) (z : B _⦋0⦌)
    (hz : prismEndpoint i A ≫ β = SSet.const z)
    (hz' : prismEndpoint i A ≫ β' = SSet.const z)
    (hβ : β = β') (hW₀ : W₀ = W₀') (hW₁ : W₁ = W₁') (he : HEq e e') :
    HEq (VertexIso.map e (curry (relativePrismEvaluationEndpoint p β i z hz)))
      (VertexIso.map e' (curry (relativePrismEvaluationEndpoint p β' i z hz'))) := by
  cases hβ
  cases hW₀
  cases hW₁
  cases eq_of_heq he
  rfl

end SerrePositivity.InfinityCategories.F2
