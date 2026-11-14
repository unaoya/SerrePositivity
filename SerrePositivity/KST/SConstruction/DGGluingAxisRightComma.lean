module
public import SerrePositivity.KST.SConstruction.CochainPostIsoInjective
public import SerrePositivity.KST.SConstruction.DGGluingAxesArrows
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.PrimitiveComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CommaComparisons.CommaStrictPostcomposition

/-! # 元の右軸包含の comma 表示の厳密成分
概要：元の右軸包含を代表加群 comma へ移しても、第三比較は零、係数射は恒等となる。
方針：元の Yoneda 鎖同型で比較零を反映し、元の右射影の恒等成分を使う。
規約：指定された同じ包含を使う。使われ方：右軸包含の全 Hom 比較 cochain。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (z : C) (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 元の右軸包含の comma 像の第三比較は、同じ零 cochain。 -/
lemma dgGluingAxisRightInclusion_comma_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (dgGluingRightAxisObject R C D M z X.right))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (𝟙_ (Complex R))
      (ForgetEnrichment.homTo (Complex R)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map
          (dgGluingAxisRightInclusion R C D M z hz X))) = 0 := by
  apply cochainPostIso_injective (dgYonedaIso R z (M.rightAt X.right))
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison_yoneda R C D M
    (dgGluingRightAxisObject R C D M z X.right) X (𝟙_ (Complex R))
    (ForgetEnrichment.homTo (Complex R) (dgGluingAxisRightInclusion R C D M z hz X))
  have hzero : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison R C D M
      (dgGluingRightAxisObject R C D M z X.right) X (𝟙_ (Complex R))
      (ForgetEnrichment.homTo (Complex R)
        (dgGluingAxisRightInclusion R C D M z hz X)) = 0 := by
    rw [dgGluingAxisRightInclusion, ForgetEnrichment.homTo_homOf]
    exact dgGluingZeroComparisonLift_comparison R C D M
      (dgGluingRightAxisObject R C D M z X.right) X
      (dgBimoduleClosedZeroLeft_value R C D M z hz X.right)
      (𝟙_ (Complex R)) 0 (eId (Complex R) X.right)
  exact (h.trans hzero).trans (Cochain.zero_comp _ _).symm

/-- 同じ comma 像の係数射は、元の右成分の恒等を保つ。 -/
lemma dgGluingAxisRightInclusion_comma_image :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (dgGluingRightAxisObject R C D M z X.right))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map
        (dgGluingAxisRightInclusion R C D M z hz X)) =
      𝟙 (ForgetEnrichment.of (Complex R) (M.rightAt X.right)) := by
  change M.toFunctor.onClosed.map
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).onClosed.map
      (dgGluingAxisRightInclusion R C D M z hz X)) = _
  rw [dgGluingAxisRightInclusion_right]
  exact M.toFunctor.onClosed.map_id _

end SerrePositivity.KST.SConstruction
