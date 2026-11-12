module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCoslicePostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetUnit
/-!
概要：元の同じ Hom(x,x) 単位から、Hom の実 coslice 全体を比較する。
方針：同じ dg 左表現可能関手の後合成と、Yoneda 単位の閉始点前合成を接続する。
規約：共通対象宇宙で扱い、入力の小ささを仮定しない。
使われ方：D(R) 値 Hom と F1 の空間値 Hom の全関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x : C)
/-- 対象だけを共通宇宙へ持ち上げた、同じ実 Hom 加群値 dg 関手。 -/
def dgHomTargetModuleLift :
    DGFunctor R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1})) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1}))
/-- 同じ Hom 単位から構成した、元の実 coslice 全体の比較射。 -/
def dgHomTargetCosliceComparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R C x ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R C) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCoslicePostcomp R (dgHomTargetModuleLift R C x) x ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecompose R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      ((dgHomTargetModuleLift R C x).obj x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R C)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x))
/-- 同じ全比較射は、元の実 Hom 関手を底に持つ。 -/
lemma dgHomTargetCosliceComparison_projection :
    dgHomTargetCosliceComparison R C x ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R C)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgHomTargetModuleLift R C x) := by
  rw [dgHomTargetCosliceComparison, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecompose_projection,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCoslicePostcomp_projection]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
