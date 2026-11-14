module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram

/-!
概要：元の区間 path 置換への射から、その全 path を保持するホモトピーを読む。
方針：元の path 射影を uncurry し、両端の引き戻し条件を照合する。
規約：指定 path を選び直さない。使われ方：終点射の境界充填の指定境界円柱。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {A X Y : SSet.{u}} (f : X ⟶ Y) (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f)

/-- 概要：元の path 置換の全 path は、元の入力像から終点へのホモトピー。
方針：path 座標を uncurry。規約：全円柱を保持。使われ方：境界で指定された path の延長。 -/
def intervalReplacementPathHomotopy :
    SSet.Homotopy ((a ≫ pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f) ≫ f)
      (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) where
  h := (β_ A (Δ[1] : SSet.{u})).hom ≫
    uncurry (a ≫ pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f)
  h₀ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ uncurry (a ≫ pullback.fst _ _) =
      (a ≫ pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f) ≫ f
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    change (a ≫ pullback.fst _ _) ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  h₁ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ uncurry (a ≫ pullback.fst _ _) = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：読んだ全ホモトピーを戻すと、元の全 path 射影そのもの。
方針：交換の二回と curry の逆則。規約：厳密な等式。使われ方：持ち上げの境界の照合。 -/
lemma intervalReplacementPathHomotopy_curry :
    curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ (intervalReplacementPathHomotopy f a).h) =
      a ≫ pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f := by
  change curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ (β_ A (Δ[1] : SSet.{u})).hom ≫
    uncurry (a ≫ pullback.fst _ _)) = _
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
