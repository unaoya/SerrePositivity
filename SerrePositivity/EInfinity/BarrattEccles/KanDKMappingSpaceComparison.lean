module

public import SerrePositivity.EInfinity.BarrattEccles.DKMappingSpaceComparison
public import SerrePositivity.EInfinity.BarrattEccles.CAlg

/-!
# 既存 CAlg_R の実際の Kan Hom と元の Map^h の高次比較

概要：元の Ex∞ 単位を保って実際の CAlgSimplicialCategory の Hom を比較する。
方針：元の anodyne 単位と同じ DK・hammock・Map^h の比較を合成する。
規約：全 Hom のホモトピー型の比較であり、π₀ だけの結論にしない。
使われ方：全自然性と元の代数射への整合の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SimplicialLocalization SerrePositivity.SimplicialModel

variable (A : Type u) [CommRing A] (X Y : CAlgSimplicialCategory A)
def cAlgMappingSpaceComparisonIso :
    AnodyneHomotopy.anodyneQ.obj (SimplicialCategory.sHom X Y) ≅
      AnodyneHomotopy.anodyneQ.obj (SSet.uliftFunctor.{u + 1, u}.obj
        (((mappingSpace A).obj (op ((cofibrantAlgebraDKInclusion A).obj X))).obj
          ((cofibrantAlgebraDKInclusion A).obj Y))) := by
  have := SSet.anodyneExtensions.Q_inverts
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom (cofibrantAlgebraRelativeCategory A) X Y))
    (localizationHomKanUnit_anodyne (cofibrantAlgebraRelativeCategory A) X Y)
  exact (asIso (AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom (cofibrantAlgebraRelativeCategory A) X Y)))).symm ≪≫
      cofibrantAlgebraDKMappingSpaceComparisonIso A X Y
lemma cAlgMappingSpaceComparisonIso_unit :
    AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom (cofibrantAlgebraRelativeCategory A) X Y)) ≫
      (cAlgMappingSpaceComparisonIso A X Y).hom =
    (cofibrantAlgebraDKMappingSpaceComparisonIso A X Y).hom := by
  have := SSet.anodyneExtensions.Q_inverts
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom (cofibrantAlgebraRelativeCategory A) X Y))
    (localizationHomKanUnit_anodyne (cofibrantAlgebraRelativeCategory A) X Y)
  change AnodyneHomotopy.anodyneQ.map _ ≫ (inv (AnodyneHomotopy.anodyneQ.map _) ≫ _) = _
  exact IsIso.hom_inv_id_assoc _ _
end SerrePositivity.EInfinity.BarrattEccles
