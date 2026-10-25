module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalTwoStepSourceAction

/-!
概要：普遍始点の二段輸送は、同じ二つの全区間の始点作用を同時に保持する。
方針：始点と係数の組を元の全輸送へ入力し、全単体で照合する。
規約：全係数を保持。使われ方：普遍四角形比較の関手空間上の作用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 普遍始点の同じ二段輸送を関手族上で読むと、元の二段始点作用そのもの。 -/
lemma diagonalTwoStepSourceAction_universal {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b c : B _⦋0⦌}
    (l : P ⟶ intervalMappingSpace a b) (r : P ⟶ intervalMappingSpace b c) :
    functorPairRight (𝟙 P) ≫ (ihom P).map
      (diagonalFiberTransport p
        (diagonalFiberTransport p (fst (vertexFiber p a) P) (snd (vertexFiber p a) P ≫ l))
        (snd (vertexFiber p a) P ≫ r)) =
      (functorPairRight l ≫ (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint) ≫
        (functorPairRight r ≫ (ihom P).map (parametrizedFiberTransportFamily p b c).endpoint) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2
