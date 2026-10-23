module

public import SerrePositivity.InfinityCategories.F2.DiagonalFiberFamilyCurry

/-!
概要：固定した全区間族による関手空間の作用の頂点は、同じ全初期値の対角輸送。
方針：同じ第二成分との組の頂点と、元の普遍輸送の後合成を計算する。
規約：同じ普遍輸送と全係数を保持。使われ方：指定始点像の恒等性の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ全区間族の作用は、元の全初期値の頂点を同じ対角輸送の頂点へ送る。 -/
lemma diagonalFiberSourceAction_vertex {E B A : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B _⦋0⦌} (f : A ⟶ vertexFiber p a) (c : A ⟶ intervalMappingSpace a b) :
    (functorPairRight c ≫ (ihom A).map
      (parametrizedFiberTransportFamily p a b).endpoint).app (Opposite.op ⦋0⦌)
        (functorVertex f) = functorVertex (diagonalFiberTransport p f c) := by
  change ((ihom A).map (parametrizedFiberTransportFamily p a b).endpoint).app _
    ((functorPairRight c).app _ (functorVertex f)) = _
  rw [functorPairRight_vertex]
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2
