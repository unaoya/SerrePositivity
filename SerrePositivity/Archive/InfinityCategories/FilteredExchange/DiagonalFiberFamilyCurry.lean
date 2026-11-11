module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.DiagonalFiberTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPair

/-!
概要：全始点族の対角輸送を、同じ全始点評価と固定した全区間族の作用へ curry する。
方針：同じ評価射と同じ区間族の組を、普遍輸送の終点へ後合成する。
規約：区間族は全係数に依存してよい。使われ方：指定始点像の恒等性の終点への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全始点族の対角終点作用は、同じ始点評価への同じ全区間族の作用の後合成。 -/
lemma diagonalFiberTransport_family_curry {E B A R : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (F : A ⊗ R ⟶ vertexFiber p a) (c : A ⟶ intervalMappingSpace a b) :
    curry (diagonalFiberTransport p F (fst A R ≫ c)) =
      (curry F ≫ functorPairRight c) ≫
        (ihom A).map (parametrizedFiberTransportFamily p a b).endpoint := by
  rw [diagonalFiberTransport, curry_natural_right]
  congr 1
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, functorPairRight, uncurry_curry]
  rw [comp_lift, ← uncurry_natural_left, Category.comp_id, uncurry_curry,
    ← Category.assoc, whiskerLeft_fst]

end SerrePositivity.InfinityCategories.F2
