module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderTransformations
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformationWhisker

/-! # 元の実写像円柱比較と全厳密 dg Hom の可換性
概要：同じ源比較・標的包含・射影の全 Hom 自然性を、元の通常成分で回収する。
方針：厳密豊穣自然変換の実成分から、前後合成の等号を取り出す。
規約：元の入力族を保持。使われ方：隣接段の実 homotopy pushout span。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の源比較は、全厳密 dg 入力 Hom に自然。 -/
lemma presentedPerfectDGKanAssemblyCylinderSource_whisker (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblySourceFunctor A r).map C D ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C)
          (presentedPerfectDGKanAssemblyCylinderSourceMap A r D) =
      (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).map C D ≫
        eHomWhiskerRight SSet (presentedPerfectDGKanAssemblyCylinderSourceMap A r C)
          ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj D) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker
    (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r)
    (presentedPerfectDGKanAssemblyCylinderSourceTransformation A r)
    (presentedPerfectDGKanAssemblyCylinderSourceMap A r)
    (presentedPerfectDGKanAssemblyCylinderSourceTransformation_app A r) C D

/-- 元の標的包含は、全厳密 dg 入力 Hom に自然。 -/
lemma presentedPerfectDGKanAssemblyCylinderTarget_whisker (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).map C D ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C)
          (presentedPerfectDGKanAssemblyCylinderTargetMap A r D) =
      (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).map C D ≫
        eHomWhiskerRight SSet (presentedPerfectDGKanAssemblyCylinderTargetMap A r C)
          ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj D) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r)
    (presentedPerfectDGKanAssemblyCylinderTargetTransformation A r)
    (presentedPerfectDGKanAssemblyCylinderTargetMap A r)
    (presentedPerfectDGKanAssemblyCylinderTargetTransformation_app A r) C D

/-- 元の実射影は、全厳密 dg 入力 Hom に自然。 -/
lemma presentedPerfectDGKanAssemblyCylinderProjection_whisker (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).map C D ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C)
          (presentedPerfectDGKanAssemblyCylinderProjectionMap A r D) =
      (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).map C D ≫
        eHomWhiskerRight SSet (presentedPerfectDGKanAssemblyCylinderProjectionMap A r C)
          ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj D) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker
    (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r)
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyCylinderProjectionTransformation A r)
    (presentedPerfectDGKanAssemblyCylinderProjectionMap A r)
    (presentedPerfectDGKanAssemblyCylinderProjectionTransformation_app A r) C D

end SerrePositivity.KST.SConstruction
