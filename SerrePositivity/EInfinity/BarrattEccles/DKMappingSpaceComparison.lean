module

public import SerrePositivity.EInfinity.BarrattEccles.DKHammockComparison
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceReducedComparison

/-!
# 実 DK Hom と元の Map^h のホモトピー型の同型

概要：元の両弱比較を同じ全代数の reduced hammock で結ぶ。
方針：元の二つの共通始域からの実際の全単体の射を使う。
規約：同じ hammock への因子化を保持する。全自然性は別に検証する。
使われ方：既存 CAlg_R の Kan Hom と Map^h の高次比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]
  (X Y : (cofibrantAlgebraRelativeCategory A).category)
def cofibrantAlgebraDKMappingSpaceComparisonIso :
    AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom (cofibrantAlgebraRelativeCategory A) X Y) ≅
      AnodyneHomotopy.anodyneQ.obj (SSet.uliftFunctor.{u + 1, u}.obj
        (((mappingSpace A).obj (op ((cofibrantAlgebraDKInclusion A).obj X))).obj
          ((cofibrantAlgebraDKInclusion A).obj Y))) :=
  cofibrantAlgebraDKHammockComparisonIso A X Y ≪≫
    (mappingSpaceReducedHammockComparisonIso A ((cofibrantAlgebraDKInclusion A).obj X)
      ((cofibrantAlgebraDKInclusion A).obj Y)).symm
lemma cofibrantAlgebraDKMappingSpaceComparisonIso_hammock :
    (cofibrantAlgebraDKMappingSpaceComparisonIso A X Y).hom ≫
        (mappingSpaceReducedHammockComparisonIso A ((cofibrantAlgebraDKInclusion A).obj X)
          ((cofibrantAlgebraDKInclusion A).obj Y)).hom =
      (cofibrantAlgebraDKHammockComparisonIso A X Y).hom := by
  simp only [cofibrantAlgebraDKMappingSpaceComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
end SerrePositivity.EInfinity.BarrattEccles
