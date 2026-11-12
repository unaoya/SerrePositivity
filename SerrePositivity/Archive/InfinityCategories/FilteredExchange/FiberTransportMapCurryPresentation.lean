module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily

/-!
概要：元の全輸送族の指定全作用比較を、同じ endpointIso の curry と同定する。
方針：元の定義をそのまま使い、同じ fiber の Kan 構造だけを明示する。
規約：指定比較を選び直さない。使われ方：直接普遍比較の型検査の展開を分割する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の全作用の指定比較は、同じ実終点の指定比較の curry そのもの。 -/
lemma fiberTransportFamily_mapIso_eq_endpoint_curry {E B K L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B) (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T U : FiberTransportFamily (b := b) p f γ) :
    T.mapIso p f γ h₁ U = FunctorIso.curry (T.endpointIso p f γ h₁ U) := rfl

end SerrePositivity.InfinityCategories.F2
