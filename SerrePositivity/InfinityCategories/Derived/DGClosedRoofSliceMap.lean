module
public import SerrePositivity.InfinityCategories.Derived.DGClosedNerveOverMap
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOver

/-! # 厳密実分母の屋根 nerve から実 dg over slice への比較

概要：実分母の厳密 over 圏の nerve を、元の指定頂点上の実 over slice へ送る。
方針：通常の全部分圏の包含と、共通宇宙を経る厳密 over 比較を合成する。
規約：この段階の標的は ambient slice。分母全部分圏への因子化は別途照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の実分母の厳密 over nerve を、元の指定頂点上の実 over slice へ送る。 -/
def dgClosedRoofSliceMap (P : Set D) (x : D) :
    nerve (DGClosedVerdierDenominators A D P x) ⟶
      sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)) :=
  nerveMap (dgClosedVerdierDenominatorProperty A D P x).ι ≫ dgClosedNerveOverMap A D x

/-- 元の実分母の厳密 nerve から、その閉零始域の nerve への射。 -/
def dgClosedRoofNerveSourceMap (P : Set D) (x : D) :
    nerve (DGClosedVerdierDenominators A D P x) ⟶ nerve (ClosedCategory A D) :=
  nerveMap (dgClosedVerdierDenominatorProperty A D P x).ι ≫ dgClosedNerveOverSourceMap A D x

omit [Small.{u} D] in
/-- 屋根比較は、元の閉零始域からの実 dg nerve 射影を厳密に回収する。 -/
lemma dgClosedRoofSliceMap_projection (P : Set D) (x : D) :
    dgClosedRoofSliceMap A D P x ≫
      sliceOverProjection ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)) =
        dgClosedRoofNerveSourceMap A D P x ≫ closedNerveInclusion A D := by
  rw [dgClosedRoofSliceMap, Category.assoc, dgClosedNerveOverMap_projection]
  rfl

end SerrePositivity.InfinityCategories
