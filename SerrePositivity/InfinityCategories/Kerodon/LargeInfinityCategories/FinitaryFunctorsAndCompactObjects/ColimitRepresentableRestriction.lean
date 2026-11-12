module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ColimitRepresentableCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan

/-!
概要：元の余極限からの全 Hom の極限錐を、同じ全パラメーター図式へ制限する。
方針：前合成後の評価を元の同じ頂点の評価へ戻し、各点の極限性を保つ。
規約：パラメーターの全単体・元の余錐・元の全共変 Hom を同時に保持する。
使われ方：κ-filtered 図式への制限と有限極限・余極限交換との接続。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
variable {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C}

/-- 元の全 Hom 極限錐を、全パラメーターの同じ図式へ制限する。 -/
def colimitRepresentableRestriction {A : SSet.{u + 1}} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D)
    (f : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone ((pre f).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.colimitRepresentableCone c)

/-- 制限後の頂点も、元の余極限頂点からの同じ全 Hom 関手への前合成そのもの。 -/
lemma colimitRepresentableRestriction_vertex {A : SSet.{u + 1}} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D)
    (f : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C) :
    (colimitRepresentableRestriction c f).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity c.vertex) := by
  rw [colimitRepresentableRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.colimitRepresentableCone_vertex]
  rfl

/-- 元の任意の全パラメーター図式への制限後も、同じ全 Hom 錐は各点極限。 -/
lemma colimitRepresentableRestriction_isPointwiseLimit {A : SSet.{u + 1}}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (f : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseLimitCone (colimitRepresentableRestriction c f) := by
  intro a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (((pre f).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.colimitRepresentableCone c))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.colimitRepresentableCone_isPointwiseLimit c hc (f.app _ a)

/-- 元の全パラメーター図式への制限は、元の関手圏の極限錐を実際に与える。 -/
lemma colimitRepresentableRestriction_isLimit {A : SSet.{u + 1}}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (f : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (colimitRepresentableRestriction c f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_pointwise _ (colimitRepresentableRestriction_isPointwiseLimit c hc f)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
