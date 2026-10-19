module
public import SerrePositivity.InfinityCategories.Derived.DGStrictRoofCategory
public import SerrePositivity.InfinityCategories.Derived.DGRoofCorrespondenceMap

/-! # 厳密屋根 nerve から実屋根の右ファイブレーションへ

概要：厳密屋根の全射列を、元の実分母と実分子を持つ実屋根の高次単体へ送る。
方針：分母・分子の nerve の二射影の始域一致から pullback に持ち上げる。
規約：独立な対象・Hom 宇宙を保つ。使われ方：指定実細分辺の一括構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元の実屋根の、固定終点へ入る実分子の slice への射影。 -/
def dgRoofCorrespondenceTarget (P : Set D) (x y : D) :
    dgRoofCorrespondence A D P x y ⟶
      sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)) :=
  pullback.fst _ _

/-- 厳密屋根の全射列から元の実分母 over 圏への射。 -/
def dgStrictRoofDenominatorMap (P : Set D) (x y : D) :
    nerve (DGStrictRoofs A D P x y) ⟶ (dgVerdierOver A D P x : SSet) :=
  nerveMap (dgStrictRoofDenominator A D P x y) ≫ dgClosedRoofVerdierMap A D P x

/-- 厳密屋根の全射列から、元の固定終点への実分子の slice への射。 -/
def dgStrictRoofNumeratorMap (P : Set D) (x y : D) :
    nerve (DGStrictRoofs A D P x y) ⟶
      sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)) :=
  nerveMap (dgStrictRoofNumerator A D P x y) ≫ dgClosedNerveOverMap A D y

/-- 厳密屋根の二射影は、元の始域の実 dg nerve への射として一致する。 -/
lemma dgStrictRoofMaps_source (P : Set D) (x y : D) :
    dgStrictRoofNumeratorMap A D P x y ≫ sliceOverProjection _ =
      dgStrictRoofDenominatorMap A D P x y ≫ dgVerdierOverSource A D P x := by
  rw [dgStrictRoofNumeratorMap, Category.assoc, dgClosedNerveOverMap_projection,
    dgStrictRoofDenominatorMap, Category.assoc, dgClosedRoofVerdierMap_source]
  rfl

/-- 元の厳密屋根 nerve の全高次単体を、元の実屋根の全空間へ送る。 -/
def dgStrictRoofNerveMap (P : Set D) (x y : D) :
    nerve (DGStrictRoofs A D P x y) ⟶ dgRoofCorrespondence A D P x y :=
  pullback.lift (dgStrictRoofNumeratorMap A D P x y)
    (dgStrictRoofDenominatorMap A D P x y) (dgStrictRoofMaps_source A D P x y)

/-- 厳密屋根 nerve の実屋根比較は、元の実分母への射影を厳密に保つ。 -/
lemma dgStrictRoofNerveMap_projection (P : Set D) (x y : D) :
    dgStrictRoofNerveMap A D P x y ≫ dgRoofCorrespondenceProjection A D P x y =
      dgStrictRoofDenominatorMap A D P x y :=
  pullback.lift_snd _ _ _

/-- 厳密屋根 nerve の実屋根比較は、指定した実分子の slice 成分を保つ。 -/
lemma dgStrictRoofNerveMap_target (P : Set D) (x y : D) :
    dgStrictRoofNerveMap A D P x y ≫ dgRoofCorrespondenceTarget A D P x y =
      dgStrictRoofNumeratorMap A D P x y :=
  pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories
