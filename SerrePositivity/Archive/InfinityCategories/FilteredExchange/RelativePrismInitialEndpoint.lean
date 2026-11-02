module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismConstantNativeAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoWhiskerVertexMap

/-!
概要：始点も動く元の相対比較の始点像と、固定区間の native 終点像を同定する。
方針：全始点評価の同じ頂点表示を保持し、指定同型の像の合成則を使う。
規約：元の指定値を保持。使われ方：最後辺の中間比較に沿う raw 値比較の移動。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B A : SSet.{u}} (p : E ⟶ B)
  (β : (Δ[1] : SSet.{u}) ⊗ A ⟶ B) (a : B _⦋0⦌)
  (h₀ : prismEndpoint 0 A ≫ β = SSet.const a)
  (W W' : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
  (f f' : A ⟶ vertexFiber p a)
  (hs : prismEndpoint 0 A ≫ W = f ≫ vertexFiberι p a)
  (hs' : prismEndpoint 0 A ≫ W' = f' ≫ vertexFiberι p a)
  (e : VertexIso (relativeFunctorVertex p β W hW) (relativeFunctorVertex p β W' hW'))
local notation "F" => relativePrismEvaluationEndpoint p β 0 a h₀

/-- 始点も動く元の二実 prism の同じ相対比較の実始点像。 -/
def relativePrismInitialEndpointIso : FunctorIso f f' :=
  vertexIsoOfEq (VertexIso.map e (curry F))
    (relativePrismEvaluationEndpoint_curry_vertex p β W hW 0 a h₀ f hs)
    (relativePrismEvaluationEndpoint_curry_vertex p β W' hW' 0 a h₀ f' hs')

/-- 固定区間の native 終点像は、同じ実始点比較の同じ普遍輸送による後合成。 -/
lemma relativePrismNativeEndpointIso_heq_initial_postcomp [LeftFibration p]
    (b : B _⦋0⦌) (h₁ : prismEndpoint 1 A ≫ β = SSet.const b)
    (v : (intervalMappingSpace a b) _⦋0⦌)
    (hv : intervalMappingCurryOfEndpoints β h₀ h₁ = SSet.const v) :
    HEq (relativePrismNativeEndpointIso p β a b h₀ h₁ W W' hW hW' f f' hs hs' e)
      ((relativePrismInitialEndpointIso p β a h₀ W W' hW hW' f f' hs hs' e).postcomp
        ((functorVertexEquiv _ _).symm
          ((parametrizedFiberTransport p a b).app (Opposite.op ⦋0⦌) v))) := by
  let t := (functorVertexEquiv _ _).symm
    ((parametrizedFiberTransport p a b).app (Opposite.op ⦋0⦌) v)
  have hm := vertexIsoOfEq_map_heq (VertexIso.map e (curry F))
    (relativePrismEvaluationEndpoint_curry_vertex p β W hW 0 a h₀ f hs)
    (relativePrismEvaluationEndpoint_curry_vertex p β W' hW' 0 a h₀ f' hs')
    ((ihom A).map t)
  exact (relativePrismNativeEndpointIso_constant_heq p β a b h₀ h₁ v hv
    W W' hW hW' f f' hs hs' e).trans
    (hm.symm.trans (functorIso_postcomp_vertexMap_heq
      (relativePrismInitialEndpointIso p β a h₀ W W' hW hW' f f' hs hs' e) t).symm)

end SerrePositivity.InfinityCategories.F2
