module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictMappedRoofCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictRoofNerveMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosedNerveFunctorNaturality

/-! # 写した閉分子を持つ厳密屋根の nerve と実屋根

概要：元の実分母の上で、像の dg 圏への任意の閉分子の全射列を実屋根へ送る。
方針：閉 nerve の dg 関手自然性で二射影の始域を一致させ、実 pullback に持ち上げる。
規約：商の Hom へ全射性を仮定しない。使われ方：指定商分子の細分辺の全次元表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 元の実分母と、その始域の像からの実射を持つ mapped 屋根の全空間。 -/
def dgMappedRoofCorrespondence (P : Set D) (x : D) (y : E) : SSet.{max u v} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)

/-- mapped 実屋根から、像の固定終点へ入る実分子の slice への射影。 -/
def dgMappedRoofCorrespondenceTarget (P : Set D) (x : D) (y : E) :
    dgMappedRoofCorrespondence A D E F P x y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :=
  pullback.fst _ _

/-- 写した閉分子の厳密屋根 nerve から、元の実分母 over 圏への射。 -/
def dgStrictMappedRoofDenominatorMap (P : Set D) (x : D) (y : E) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictMappedRoofs A D E F P x y) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofDenominator A D E F P x y) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x

/-- 写した閉分子の厳密屋根 nerve から、像の固定終点の実 slice への射。 -/
def dgStrictMappedRoofNumeratorMap (P : Set D) (x : D) (y : E) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictMappedRoofs A D E F P x y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofNumerator A D E F P x y) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A E y

/-- 写した閉分子の厳密屋根の二射影は、元の始域の dg 関手像で一致する。 -/
lemma dgStrictMappedRoofMaps_source (P : Set D) (x : D) (y : E) :
    dgStrictMappedRoofNumeratorMap A D E F P x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      dgStrictMappedRoofDenominatorMap A D E F P x y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  rw [dgStrictMappedRoofNumeratorMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap_projection,
    dgStrictMappedRoofDenominatorMap, Category.assoc,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap_source]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion_dgFunctor]
  rfl

/-- 写した閉分子の厳密屋根の全射列を、同じ元の実分母上の実屋根へ送る。 -/
def dgStrictMappedRoofNerveMap (P : Set D) (x : D) (y : E) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictMappedRoofs A D E F P x y) ⟶ dgMappedRoofCorrespondence A D E F P x y :=
  pullback.lift (dgStrictMappedRoofNumeratorMap A D E F P x y)
    (dgStrictMappedRoofDenominatorMap A D E F P x y) (dgStrictMappedRoofMaps_source A D E F P x y)

/-- 写した閉分子の厳密屋根比較は、元の実分母の射列を厳密に保つ。 -/
lemma dgStrictMappedRoofNerveMap_projection (P : Set D) (x : D) (y : E) :
    dgStrictMappedRoofNerveMap A D E F P x y ≫ pullback.snd _ _ =
      dgStrictMappedRoofDenominatorMap A D E F P x y :=
  pullback.lift_snd _ _ _

/-- 写した閉分子の厳密屋根比較は、指定実分子の slice 成分を保つ。 -/
lemma dgStrictMappedRoofNerveMap_target (P : Set D) (x : D) (y : E) :
    dgStrictMappedRoofNerveMap A D E F P x y ≫ dgMappedRoofCorrespondenceTarget A D E F P x y =
      dgStrictMappedRoofNumeratorMap A D E F P x y :=
  pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
