module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderPushout
public import SerrePositivity.KST.SConstruction.PointedDoubleMappingCylinderMono

/-! # 元の隣接段円柱比較と押し出しの基礎単射
概要：元の源比較・標的包含と、元の両標的から押し出し候補への射の単射性を供給する。
方針：同じ元の点つき写像円柱・二脚押し出しの無条件の単射性を適用する。
規約：右脚の単射性は仮定しない。使われ方：BF の単射構造射の構成。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の同じ左脚の実円柱源比較は、基礎単体集合上で単射。 -/
lemma presentedPerfectDGKanAssemblyCylinderSourceMap_mono (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    Mono (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderSourceMap A r C).right :=
  pointedTensorMappingCylinderSource_mono
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyLeftMap A r C)

/-- 元の同じ左標的からの実円柱包含も、基礎単体集合上で単射。 -/
lemma presentedPerfectDGKanAssemblyCylinderTargetMap_mono (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    Mono (show ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderTargetMap A r C).right :=
  pointedTensorMappingCylinderTarget_mono
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyLeftMap A r C)

/-- 元の同じ左標的から、円柱を貼り付けた同じ実押し出しへの比較。 -/
def presentedPerfectDGKanAssemblyCylinderPushoutLeftMap (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C :=
  presentedPerfectDGKanAssemblyCylinderTargetMap A r C ≫
    pointedSpanPushoutInl ((presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).obj C)

/-- 元の同じ右標的から、円柱を貼り付けた同じ実押し出しへの包含。 -/
def presentedPerfectDGKanAssemblyCylinderPushoutRightMap (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyTargetFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C :=
  pointedSpanPushoutInr ((presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).obj C)

/-- 元の左標的から同じ実押し出しへの比較は、基礎単体集合上で単射。 -/
lemma presentedPerfectDGKanAssemblyCylinderPushoutLeftMap_mono (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    Mono (show ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderPushoutLeftMap A r C).right :=
  pointedDoubleMappingCylinderLeft_mono
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyLeftMap A r C)
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyRightMap A r C)

/-- 元の右標的から同じ実押し出しへの包含も、基礎単体集合上で単射。 -/
lemma presentedPerfectDGKanAssemblyCylinderPushoutRightMap_mono (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    Mono (show ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r C).right :=
  pointedDoubleMappingCylinderRight_mono
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyLeftMap A r C)
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyRightMap A r C)

end SerrePositivity.KST.SConstruction
