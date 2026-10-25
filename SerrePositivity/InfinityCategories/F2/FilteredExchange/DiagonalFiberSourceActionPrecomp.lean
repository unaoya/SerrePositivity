module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalFiberSourceIsoAction

/-!
概要：同じ区間族の始点作用は、全係数の制限と厳密に可換。
方針：同じ元の普遍輸送の評価を、関手空間の全単体で照合する。
規約：始点・区間族・全係数を保持。使われ方：指定 sourceIso の係数自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の同じ全区間作用は、任意の係数制限を保つ。 -/
lemma diagonalFiberSourceAction_precomp {E B P Q : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (c : P ⟶ intervalMappingSpace a b) (q : Q ⟶ P) :
    (functorPairRight c ≫ (ihom P).map
        (parametrizedFiberTransportFamily p a b).endpoint) ≫
        (pre q).app (vertexFiber p b) =
      (pre q).app (vertexFiber p a) ≫
        (functorPairRight (q ≫ c) ≫ (ihom Q).map
          (parametrizedFiberTransportFamily p a b).endpoint) := by
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
