module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Fiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorFiberHom

/-!
概要：相対 Hom の宇宙移送は、同じ fiber の全 Hom 作用に厳密に自然。
方針：内部 Hom と fiber の持ち上げ同型を用い、元の評価の各単体の ULift を照合する。
規約：充填性は不要。異なる宇宙の間の単体集合の射は作らない。
使われ方：小さい unstraightening の比較の fiber 作用を元の c1 の輸送へ戻す。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 相対 Hom の持ち上げは、同じ指定 fiber の Hom 作用を厳密に保つ。 -/
lemma uliftRelativeFunctorMap_fiberHom {A E B : SSet.{u}}
    (a : A ⟶ B) (p : E ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorMap.{u, v} p a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorFiberHom ((SSet.uliftFunctor.{v, u}).map a)
        ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) =
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorFiberHom a p b) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber a b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)).hom ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftVertexFiberIso.{u, v} a b).inv).app
        ((SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)) ≫
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((SSet.uliftFunctor.{v, u}).map a) (ULift.up b))).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftVertexFiberIso.{u, v} p b).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
