module
public import SerrePositivity.KST.SConstruction.DGGluingAxesOrthogonal
public import SerrePositivity.KST.SConstruction.DGBimoduleAxisZero
public import SerrePositivity.KST.SConstruction.DGGluingZeroComparisonLift

/-! # 元の gluing 対象と指定二軸を結ぶ実閉射
概要：同じ元の対象へ右軸から入り、同じ対象から左軸へ出る実閉射を構成する。
方針：双加群の実零値で比較境界を消し、元の二成分 (0,id)・(id,0) を持ち上げる。
規約：元の対象と指定閉零対象を保持。使われ方：二軸分解の cofiber 比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))

/-- 元の対象に、その同じ右成分の実右軸から入る閉射。 -/
def dgGluingAxisRightInclusion (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ForgetEnrichment.of (Complex R) (dgGluingRightAxisObject R C D M zc X.right) ⟶
      ForgetEnrichment.of (Complex R) X :=
  ForgetEnrichment.homOf (Complex R)
    (dgGluingZeroComparisonLift R C D M (dgGluingRightAxisObject R C D M zc X.right) X
      (dgBimoduleClosedZeroLeft_value R C D M zc hc X.right)
      (𝟙_ (Complex R)) 0 (eId (Complex R) X.right))

/-- 元の対象から、その同じ左成分の実左軸へ出る閉射。 -/
def dgGluingAxisLeftProjection (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ForgetEnrichment.of (Complex R) X ⟶
      ForgetEnrichment.of (Complex R) (dgGluingLeftAxisObject R C D M zd X.left) :=
  ForgetEnrichment.homOf (Complex R)
    (dgGluingZeroComparisonLift R C D M X (dgGluingLeftAxisObject R C D M zd X.left)
      (dgBimoduleClosedZeroRight_value R C D M zd hd X.left)
      (𝟙_ (Complex R)) (eId (Complex R) X.left) 0)

/-- 同じ右軸からの射の右成分は、元の恒等射。 -/
lemma dgGluingAxisRightInclusion_right (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).onClosed.map
      (dgGluingAxisRightInclusion R C D M zc hc X) = 𝟙 (ForgetEnrichment.of (Complex R) X.right) :=
  (congrArg (ForgetEnrichment.homOf (Complex R))
    ((congrArg (fun k => dgGluingZeroComparisonLift R C D M
      (dgGluingRightAxisObject R C D M zc X.right) X
        (dgBimoduleClosedZeroLeft_value R C D M zc hc X.right)
      (𝟙_ (Complex R)) 0 (eId (Complex R) X.right) ≫ k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map R C D M (dgGluingRightAxisObject R C D M zc X.right) X)).trans
        (dgGluingZeroComparisonLift_right R C D M
      (dgGluingRightAxisObject R C D M zc X.right) X
        (dgBimoduleClosedZeroLeft_value R C D M zc hc X.right)
      (𝟙_ (Complex R)) 0 (eId (Complex R) X.right)))).trans (by rfl)

/-- 同じ右軸からの射の左成分は、元の零射。 -/
lemma dgGluingAxisRightInclusion_left (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).onClosed.map
      (dgGluingAxisRightInclusion R C D M zc hc X) = 0 :=
  (congrArg (ForgetEnrichment.homOf (Complex R))
    (dgGluingZeroComparisonLift_left R C D M
      (dgGluingRightAxisObject R C D M zc X.right) X
        (dgBimoduleClosedZeroLeft_value R C D M zc hc X.right)
      (𝟙_ (Complex R)) 0 (eId (Complex R) X.right))).trans (by rfl)

/-- 同じ左軸への射の左成分は、元の恒等射。 -/
lemma dgGluingAxisLeftProjection_left (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).onClosed.map
      (dgGluingAxisLeftProjection R C D M zd hd X) = 𝟙 (ForgetEnrichment.of (Complex R) X.left) :=
  (congrArg (ForgetEnrichment.homOf (Complex R))
    (dgGluingZeroComparisonLift_left R C D M
      X (dgGluingLeftAxisObject R C D M zd X.left)
        (dgBimoduleClosedZeroRight_value R C D M zd hd X.left)
      (𝟙_ (Complex R)) (eId (Complex R) X.left) 0)).trans (by rfl)

/-- 同じ左軸への射の右成分は、元の零射。 -/
lemma dgGluingAxisLeftProjection_right (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).onClosed.map
      (dgGluingAxisLeftProjection R C D M zd hd X) = 0 :=
  (congrArg (ForgetEnrichment.homOf (Complex R))
    ((congrArg (fun k => dgGluingZeroComparisonLift R C D M
      X (dgGluingLeftAxisObject R C D M zd X.left)
        (dgBimoduleClosedZeroRight_value R C D M zd hd X.left)
      (𝟙_ (Complex R)) (eId (Complex R) X.left) 0 ≫ k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map R C D M X (dgGluingLeftAxisObject R C D M zd X.left))).trans
        (dgGluingZeroComparisonLift_right R C D M
      X (dgGluingLeftAxisObject R C D M zd X.left)
        (dgBimoduleClosedZeroRight_value R C D M zd hd X.left)
      (𝟙_ (Complex R)) (eId (Complex R) X.left) 0))).trans (by rfl)

end SerrePositivity.KST.SConstruction
