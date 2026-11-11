module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLifting

/-!
概要：元の自明 Kan fibration は宇宙を持ち上げても同じ全境界持ち上げを保つ。
方針：境界包含の宇宙移送の同値を各次元に適用する。
規約：モデル圏の存在を追加仮定にしない。
使われ方：元の native core の source Segal 制限の宇宙移送。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 元の同じ自明 Kan 射の宇宙持ち上げも自明 Kan。 -/
lemma trivialKanFibration_uliftFunctor_map {X Y : SSet.{u}} (p : X ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((SSet.uliftFunctor.{v, u}).map p) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  exact (SimplicialModel.UniverseLift.boundary_lifting_iff p n).mpr
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary p).mp inferInstance n)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
