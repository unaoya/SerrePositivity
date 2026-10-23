module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.MarkedCocartesianFunctorPrecomposition
public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativeComposition

/-!
概要：元の cocartesian 相対 Hom を、cocartesian 辺を保つ底上の射で前合成する。
方針：指定辺を保つ相対 Hom の制限を、元の cocartesian 辺の集合に適用する。
規約：射影や前合成の射に fibration 性や単射性を要求しない。
使われ方：元の全 cocartesian Hom の余極限に沿う降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の cocartesian 辺を保つ底上の射による、元の全 cocartesian 相対 Hom の制限。 -/
def cocartesianRelativeFunctorPre {E B : SSet.{u}} (q : E ⟶ B) {a b : Over B}
    (i : a ⟶ b) (hi : PreservesCocartesianEdges a.hom b.hom i.left) :
    cocartesianRelativeFunctorSpace b.hom q ⟶ cocartesianRelativeFunctorSpace a.hom q :=
  markedCocartesianFunctorPre q i {e | IsCocartesianEdge a.hom e}
    {e | IsCocartesianEdge b.hom e} hi

/-- 元の cocartesian Hom の制限は、包含後に同じ全相対 Hom の前合成。 -/
lemma cocartesianRelativeFunctorPre_ι {E B : SSet.{u}} (q : E ⟶ B) {a b : Over B}
    (i : a ⟶ b) (hi : PreservesCocartesianEdges a.hom b.hom i.left) :
    cocartesianRelativeFunctorPre q i hi ≫ cocartesianRelativeFunctorInclusion a.hom q =
      cocartesianRelativeFunctorInclusion b.hom q ≫ relativeFunctorOverPre q i :=
  markedCocartesianFunctorPre_ι _ _ _ _ _

end SerrePositivity.InfinityCategories
