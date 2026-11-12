module

public import SerrePositivity.EInfinity.BarrattEccles.DKMappingSpaceNaturality
public import SerrePositivity.EInfinity.BarrattEccles.KanDKMappingSpaceComparison

/-!
# 同じ Ex∞ による Kan DK/Map^h 比較の自然性

概要：元の実 DK Hom の前後合成を同じ Ex∞ で送った作用を比較する。
方針：元の Ex∞ 単位の自然性と既存比較の単位での回収式を使う。
規約：元の Kan 化・元の比較・元の Map^h を保持する。
使われ方：CAlg_R の実 Kan Hom の高次比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SimplicialLocalization SerrePositivity.SimplicialModel

variable (A : Type u) [CommRing A]

lemma cAlgMappingSpaceComparisonIso_postcompose
    (X : (cofibrantAlgebraRelativeCategory A).category)
    {Y Z : (cofibrantAlgebraRelativeCategory A).category} (g : Y ⟶ Z) :
    AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationPostcompose (cofibrantAlgebraRelativeCategory A) X g)) ≫
      (cAlgMappingSpaceComparisonIso A X Z).hom =
    (cAlgMappingSpaceComparisonIso A X Y).hom ≫
      AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
        (((mappingSpace A).obj (op ((cofibrantAlgebraDKInclusion A).obj X))).map
          ((cofibrantAlgebraDKInclusion A).map g))) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hu := localizationHomKanUnit_anodyne (cofibrantAlgebraRelativeCategory A) X Y
  have := SSet.anodyneExtensions.Q_inverts
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom (cofibrantAlgebraRelativeCategory A) X Y)) hu
  have h := congrArg Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality
    (localizationPostcompose (cofibrantAlgebraRelativeCategory A) X g))
  simp only [Functor.id_map, Functor.map_comp] at h
  apply (cancel_epi (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
    (localizationHom (cofibrantAlgebraRelativeCategory A) X Y)))).1
  rw [← Category.assoc, ← h, Category.assoc, cAlgMappingSpaceComparisonIso_unit,
    ← Category.assoc, cAlgMappingSpaceComparisonIso_unit,
    cofibrantAlgebraDKMappingSpaceComparisonIso_postcompose]

lemma cAlgMappingSpaceComparisonIso_precompose
    (Z : (cofibrantAlgebraRelativeCategory A).category)
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y) :
    AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationPrecompose (cofibrantAlgebraRelativeCategory A) Z f)) ≫
      (cAlgMappingSpaceComparisonIso A X Z).hom =
    (cAlgMappingSpaceComparisonIso A Y Z).hom ≫
      AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
        (((mappingSpace A).map ((cofibrantAlgebraDKInclusion A).map f).op).app
          ((cofibrantAlgebraDKInclusion A).obj Z))) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hu := localizationHomKanUnit_anodyne (cofibrantAlgebraRelativeCategory A) Y Z
  have := SSet.anodyneExtensions.Q_inverts
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom (cofibrantAlgebraRelativeCategory A) Y Z)) hu
  have h := congrArg Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality
    (localizationPrecompose (cofibrantAlgebraRelativeCategory A) Z f))
  simp only [Functor.id_map, Functor.map_comp] at h
  apply (cancel_epi (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
    (localizationHom (cofibrantAlgebraRelativeCategory A) Y Z)))).1
  rw [← Category.assoc, ← h, Category.assoc, cAlgMappingSpaceComparisonIso_unit,
    ← Category.assoc, cAlgMappingSpaceComparisonIso_unit,
    cofibrantAlgebraDKMappingSpaceComparisonIso_precompose]

end SerrePositivity.EInfinity.BarrattEccles
