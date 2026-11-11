module

public import SerrePositivity.EInfinity.Hammock.AnodyneComponents
public import SerrePositivity.EInfinity.BarrattEccles.KanDKMappingSpaceNaturality

/-!
# 既存の高次比較が誘導する元の連結成分の同型

概要：同じ Map^h・実 DK Hom・実 Kan Hom の比較へ π₀ を作用させる。
方針：元の anodyne 局所化への π₀ の因子化で元の左右射を回収する。
規約：以前の零次の同値との一致は別に証明し、同型を選び直さない。
使われ方：高次比較の既存 π₀ 比較との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SimplicialLocalization Hammock

variable (A : Type u) [CommRing A]

def mappingSpaceReducedHammockComponentsIso (X Y : (operad A).Algebra) :
    SSet.π₀ (SSet.uliftFunctor.{u + 1, u}.obj (((mappingSpace A).obj (op X)).obj Y)) ≅
      SSet.π₀ (algebraReducedHammock A X Y) :=
  AnodyneComponents.iso (mappingSpaceReducedHammockComparisonIso A X Y)

lemma mappingSpaceReducedHammockComponentsIso_fac (X Y : (operad A).Algebra) :
    SSet.π₀Functor.map (mappingSpaceIndexAugmentation A X Y) ≫
        (mappingSpaceReducedHammockComponentsIso A X Y).hom =
      SSet.π₀Functor.map (mappingSpaceReducedHammockNerveMap A X Y) :=
  AnodyneComponents.iso_fac _ _ _ (mappingSpaceReducedHammockComparisonIso_fac A X Y)

def cofibrantAlgebraDKMappingSpaceComponentsIso
    (X Y : (cofibrantAlgebraRelativeCategory A).category) :
    SSet.π₀ (localizationHom (cofibrantAlgebraRelativeCategory A) X Y) ≅
      SSet.π₀ (SSet.uliftFunctor.{u + 1, u}.obj
        (((mappingSpace A).obj (op ((cofibrantAlgebraDKInclusion A).obj X))).obj
          ((cofibrantAlgebraDKInclusion A).obj Y))) :=
  AnodyneComponents.iso (cofibrantAlgebraDKMappingSpaceComparisonIso A X Y)

lemma cofibrantAlgebraDKMappingSpaceComponentsIso_hammock
    (X Y : (cofibrantAlgebraRelativeCategory A).category) :
    (cofibrantAlgebraDKMappingSpaceComponentsIso A X Y).hom ≫
        (mappingSpaceReducedHammockComponentsIso A ((cofibrantAlgebraDKInclusion A).obj X)
          ((cofibrantAlgebraDKInclusion A).obj Y)).hom =
      (AnodyneComponents.iso (cofibrantAlgebraDKHammockComparisonIso A X Y)).hom := by
  have h := congrArg AnodyneComponents.map
    (cofibrantAlgebraDKMappingSpaceComparisonIso_hammock A X Y)
  simpa only [cofibrantAlgebraDKMappingSpaceComponentsIso,
    mappingSpaceReducedHammockComponentsIso, AnodyneComponents.map_comp,
    ← AnodyneComponents.iso_hom] using h

def cAlgMappingSpaceComponentsIso (X Y : CAlgSimplicialCategory A) :
    SSet.π₀ (SimplicialCategory.sHom X Y) ≅
      SSet.π₀ (SSet.uliftFunctor.{u + 1, u}.obj
        (((mappingSpace A).obj (op ((cofibrantAlgebraDKInclusion A).obj X))).obj
          ((cofibrantAlgebraDKInclusion A).obj Y))) :=
  AnodyneComponents.iso (cAlgMappingSpaceComparisonIso A X Y)

lemma cAlgMappingSpaceComponentsIso_unit (X Y : CAlgSimplicialCategory A) :
    SSet.π₀Functor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
        (localizationHom (cofibrantAlgebraRelativeCategory A) X Y)) ≫
      (cAlgMappingSpaceComponentsIso A X Y).hom =
    (cofibrantAlgebraDKMappingSpaceComponentsIso A X Y).hom := by
  have h := congrArg AnodyneComponents.map (cAlgMappingSpaceComparisonIso_unit A X Y)
  simpa only [cAlgMappingSpaceComponentsIso, cofibrantAlgebraDKMappingSpaceComponentsIso,
    AnodyneComponents.map_comp, AnodyneComponents.map_actual,
    ← AnodyneComponents.iso_hom] using h

end SerrePositivity.EInfinity.BarrattEccles
