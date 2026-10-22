module
public import SerrePositivity.KST.SConstruction.PointedTensorMappingCylinderWeakEquivalence
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderComparisons
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyLeftEquivalence

/-! # 元の隣接段の同じ写像円柱の弱比較
概要：元の左脚の実写像円柱の射影と源比較は、anodyne 局所化で可逆。
方針：同じ実写像円柱の一般定理と、元の左脚の局所化可逆性を適用する。
規約：全 Hom 自然な元の成分を保持する。使われ方：関手的 BF 帰納置換。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

/-- 元の同じ実写像円柱の 標的包含の弱同値性。 -/
lemma presentedPerfectDGKanAssemblyCylinderTargetMap_anodyne (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    anodyneExtensions
      (show ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj ⟶
        ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C).obj from
          presentedPerfectDGKanAssemblyCylinderTargetMap A r C).right := by
  erw [presentedPerfectDGKanAssemblyCylinderTargetMap_eq]
  exact pointedTensorMappingCylinderTarget_anodyne _

/-- 元の同じ実写像円柱の 射影の弱同値性。 -/
lemma presentedPerfectDGKanAssemblyCylinderProjectionMap_localized_isIso (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C).obj ⟶
        ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
          presentedPerfectDGKanAssemblyCylinderProjectionMap A r C).right) := by
  erw [presentedPerfectDGKanAssemblyCylinderProjectionMap_eq]
  exact pointedTensorMappingCylinderProjection_localized_isIso
    AnodyneHomotopy.anodyneQ (Localization.inverts _ anodyneExtensions) _

/-- 元の同じ実写像円柱の 源比較の弱同値性。 -/
lemma presentedPerfectDGKanAssemblyCylinderSourceMap_localized_isIso (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
        ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C).obj from
          presentedPerfectDGKanAssemblyCylinderSourceMap A r C).right) := by
  erw [presentedPerfectDGKanAssemblyCylinderSourceMap_eq]
  let _ := presentedPerfectDGKanAssemblyLeftMap_localized_isIso A r C
  exact pointedTensorMappingCylinderSource_localized_isIso
    AnodyneHomotopy.anodyneQ (Localization.inverts _ anodyneExtensions) _

end SerrePositivity.KST.SConstruction
