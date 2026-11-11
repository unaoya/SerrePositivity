module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorSpace

/-!
概要：内部 Hom の宇宙持ち上げ同型の指定頂点への作用を計算する。
方針：元の関手頂点の各次数の評価を比較する。
規約：元の射を持ち上げ、射や頂点を選び直さない。
使われ方：小さい全切断の恒等射比較を大きい実際の射へ移す。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 内部 Hom の持ち上げ同型は、指定関手の頂点を同じ関手の持ち上げへ写す。 -/
lemma uliftFunctorSpaceIso_hom_vertex {A X : SSet.{u}} (f : A ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso.{u, v} A X).hom.app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{v, u}).map f) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
