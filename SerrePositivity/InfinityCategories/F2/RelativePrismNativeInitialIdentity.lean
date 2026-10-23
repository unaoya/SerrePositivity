module

public import SerrePositivity.InfinityCategories.F2.RelativePrismNativeInitialAction
public import SerrePositivity.InfinityCategories.F2.RelativePrismInitialEndpoint
public import SerrePositivity.InfinityCategories.F2.DiagonalFiberSourceVertex
public import SerrePositivity.InfinityCategories.F2.VertexIsoIdentityFactor

/-!
概要：元の相対比較の指定始点像が恒等なら、同じ native 指定終点像も恒等となる。
方針：同じ全区間族の作用への因数分解と、元の実頂点等式を使う。
規約：HEq から端点等式を取り出さない。使われ方：零面比較の中間因子の消去。
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
  (f : A ⟶ vertexFiber p a)
  (hs : prismEndpoint 0 A ≫ W = f ≫ vertexFiberι p a)
  (hs' : prismEndpoint 0 A ≫ W' = f ≫ vertexFiberι p a)
  (e : VertexIso (relativeFunctorVertex p β W hW) (relativeFunctorVertex p β W' hW'))
local notation "F" => relativePrismEvaluationEndpoint p β 0 a h₀
local notation "c" => intervalMappingCurryOfEndpoints β h₀ h₁
local notation "Ω" => functorPairRight c ≫
  CategoryTheory.Functor.map (ihom A)
    (FiberTransportFamily.endpoint (parametrizedFiberTransportFamily p a b))
local notation "I" => relativePrismInitialEndpointIso p β a h₀ W W' hW hW' f f hs hs' e
local notation "N" => relativePrismNativeEndpointIso p β a b h₀ h₁ W W' hW hW' f f hs hs' e

/-- 元の指定始点像が恒等なら、同じ全区間族に沿う native 指定終点像も厳密に恒等。 -/
lemma relativePrismNativeEndpointIso_eq_refl_of_initial (hI : I = Iso.refl _) :
    N = Iso.refl _ := by
  have hn := relativePrismNativeEndpointIso_heq_initial_action p β a b h₀ h₁
    W W' hW hW' f f hs hs' e
  have hm : HEq (VertexIso.map I Ω) (VertexIso.map (VertexIso.map e (curry F)) Ω) :=
    vertexIsoOfEq_map_heq (VertexIso.map e (curry F))
      (relativePrismEvaluationEndpoint_curry_vertex p β W hW 0 a h₀ f hs)
      (relativePrismEvaluationEndpoint_curry_vertex p β W' hW' 0 a h₀ f hs') Ω
  have hmap := vertexIso_map_heq_refl_of_heq I rfl (heq_of_eq hI) Ω
  have hi : HEq
      (Iso.refl (SSet.HomotopyCategory.mk (NatTrans.app Ω (Opposite.op ⦋0⦌) (functorVertex f))))
      (Iso.refl (SSet.HomotopyCategory.mk (functorVertex (diagonalFiberTransport p f c)))) := by
    rw [diagonalFiberSourceAction_vertex]
  exact eq_of_heq (hn.trans (hm.symm.trans (hmap.trans hi)))

end SerrePositivity.InfinityCategories.F2
