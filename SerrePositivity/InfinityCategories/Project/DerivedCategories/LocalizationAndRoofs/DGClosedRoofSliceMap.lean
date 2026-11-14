module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGClosedNerveOverMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOver

/-! # 厳密実分母の屋根 nerve から実 dg over slice への比較

概要：実分母の厳密 over 圏の nerve を、元の指定頂点上の実 over slice へ送る。
方針：通常の全部分圏の包含と、共通宇宙を経る厳密 over 比較を合成する。
規約：この段階の標的は ambient slice。分母全部分圏への因子化は別途照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 元の実分母の厳密 over nerve を、元の指定頂点上の実 over slice へ送る。 -/
def dgClosedRoofSliceMap (P : Set D) (x : D) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorProperty A D P x).ι ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A D x

/-- 元の実分母の厳密 nerve から、その閉零始域の nerve への射。 -/
def dgClosedRoofNerveSourceMap (P : Set D) (x : D) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) ⟶ nerve (ClosedCategory A D) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorProperty A D P x).ι ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverSourceMap A D x

omit [Small.{u} D] in
/-- 屋根比較は、元の閉零始域からの実 dg nerve 射影を厳密に回収する。 -/
lemma dgClosedRoofSliceMap_projection (P : Set D) (x : D) :
    dgClosedRoofSliceMap A D P x ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) =
        dgClosedRoofNerveSourceMap A D P x ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A D := by
  rw [dgClosedRoofSliceMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap_projection]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
