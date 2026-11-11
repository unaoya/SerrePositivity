module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeComposition

/-!
概要：元の cocartesian 相対 Hom を、cocartesian 辺を保つ底上の射で前合成する。
方針：指定辺を保つ相対 Hom の制限を、元の cocartesian 辺の集合に適用する。
規約：射影や前合成の射に fibration 性や単射性を要求しない。
使われ方：元の全 cocartesian Hom の余極限に沿う降下。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の cocartesian 辺を保つ底上の射による、元の全 cocartesian 相対 Hom の制限。 -/
def cocartesianRelativeFunctorPre {E B : SSet.{u}} (q : E ⟶ B) {a b : Over B}
    (i : a ⟶ b) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges a.hom b.hom i.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace b.hom q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace a.hom q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q i {e | _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge a.hom e}
    {e | _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge b.hom e} hi

/-- 元の cocartesian Hom の制限は、包含後に同じ全相対 Hom の前合成。 -/
lemma cocartesianRelativeFunctorPre_ι {E B : SSet.{u}} (q : E ⟶ B) {a b : Over B}
    (i : a ⟶ b) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges a.hom b.hom i.left) :
    cocartesianRelativeFunctorPre q i hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorInclusion a.hom q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorInclusion b.hom q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
