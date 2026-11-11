module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomCalculus
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaProjections
public import SerrePositivity.DifferentialGraded.Category.ObjectImage
public import SerrePositivity.DifferentialGraded.Module.Graded

/-!
双加群 gluing の代表加群表示。
閉元 μ を Yoneda で h_c → M(d) に変換し、既存 comma dg 圏の充満対象族を取る。
単位・合成・微分の両立と結合律は実 comma の全 Hom 上の法則から従う。
native Hom 複体との比較、前三角性および nerve 比較は別途証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 同じ閉元の、代表加群からの閉零射としての Yoneda 拡張。 -/
def dgGluingAugmentation (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ForgetEnrichment.of (Complex R) (representable R X.left) ⟶
      ForgetEnrichment.of (Complex R) (M.rightAt X.right) :=
  ForgetEnrichment.homOf (Complex R)
    (X.gluingMap ≫ (dgYonedaIso R X.left (M.rightAt X.right)).inv)

/-- 代表加群表示から同じ元の閉元の鎖写像を厳密に回収する。 -/
lemma dgGluingAugmentation_value (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ForgetEnrichment.homTo (Complex R) (dgGluingAugmentation R C D M X) ≫
      (dgYonedaIso R X.left (M.rightAt X.right)).hom = X.gluingMap := by
  simp only [dgGluingAugmentation, ForgetEnrichment.homTo_homOf, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- 双加群 gluing の対象を、同じ比較射を保持する実 comma の対象として読む。 -/
def dgGluingCommaObject (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor where
  source := X.right
  replacement := representable R X.left
  augmentation := dgGluingAugmentation R C D M X

/-- 代表加群表示における dg gluing 圏。全 Hom・単位・合成は実 comma のもの。 -/
abbrev DGGluingRepresentableCategory := _root_.SerrePositivity.InfinityCategories.DGObjectImage (dgGluingCommaObject R C D M)

/-- 実 comma への充満 dg 関手。 -/
def dgGluingRepresentableToComma :
    DGFunctor R (DGGluingRepresentableCategory R C D M)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor) :=
  _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation R (dgGluingCommaObject R C D M)

/-- 右成分への実 dg 射影。 -/
def dgGluingRepresentableRight : DGFunctor R (DGGluingRepresentableCategory R C D M) D :=
  (dgGluingRepresentableToComma R C D M).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R D (RightModule R C) M.toFunctor)

/-- 左成分の代表加群への実 dg 射影。 -/
def dgGluingRepresentableLeftModule :
    DGFunctor R (DGGluingRepresentableCategory R C D M) (RightModule R C) :=
  (dgGluingRepresentableToComma R C D M).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R D (RightModule R C) M.toFunctor)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
