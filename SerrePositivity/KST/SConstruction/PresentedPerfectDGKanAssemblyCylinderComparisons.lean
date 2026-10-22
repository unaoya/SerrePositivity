module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyLeftCylinder
public import SerrePositivity.KST.SConstruction.PointedEnrichedMappingCylinderComponents

/-! # 元の隣接段左脚の実写像円柱比較
概要：元の厳密 dg 入力上で、源比較・標的包含・射影を同じ実射として保持する。
方針：元の左脚に対する豊穣写像円柱の実成分を使う。
規約：自然な逆を選ばない。使われ方：BF の単射置換と元の組み立てとの比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の源から同じ左脚の実写像円柱への比較。 -/
def presentedPerfectDGKanAssemblyCylinderSourceMap (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblySourceFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C :=
  pointedEnrichedMappingCylinderSource (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyLeftMap A r) (presentedPerfectDGKanAssemblyLeft_whisker A r) C

/-- 元の左標的から同じ実写像円柱への包含。 -/
def presentedPerfectDGKanAssemblyCylinderTargetMap (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C :=
  pointedEnrichedMappingCylinderTarget (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyLeftMap A r) (presentedPerfectDGKanAssemblyLeft_whisker A r) C

/-- 同じ元の実写像円柱から元の左標的への射影。 -/
def presentedPerfectDGKanAssemblyCylinderProjectionMap (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C :=
  pointedEnrichedMappingCylinderProjection (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyLeftMap A r) (presentedPerfectDGKanAssemblyLeft_whisker A r) C

/-- 源比較は、同じ元の左脚の点つき写像円柱源射そのもの。 -/
lemma presentedPerfectDGKanAssemblyCylinderSourceMap_eq (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderSourceMap A r C) =
      pointedTensorMappingCylinderSource
        (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
          ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
            presentedPerfectDGKanAssemblyLeftMap A r C) := rfl

/-- 標的包含は、同じ元の左脚の点つき写像円柱標的射そのもの。 -/
lemma presentedPerfectDGKanAssemblyCylinderTargetMap_eq (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (show ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderTargetMap A r C) =
      pointedTensorMappingCylinderTarget
        (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
          ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
            presentedPerfectDGKanAssemblyLeftMap A r C) := rfl

/-- 射影は、同じ元の左脚の点つき写像円柱射影そのもの。 -/
lemma presentedPerfectDGKanAssemblyCylinderProjectionMap_eq (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (show ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderProjectionMap A r C) =
      pointedTensorMappingCylinderProjection
        (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
          ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
            presentedPerfectDGKanAssemblyLeftMap A r C) := rfl

/-- 元の標的包含と射影の合成は、元の同じ標的の恒等射。 -/
lemma presentedPerfectDGKanAssemblyCylinderTarget_projection (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    presentedPerfectDGKanAssemblyCylinderTargetMap A r C ≫
      presentedPerfectDGKanAssemblyCylinderProjectionMap A r C = 𝟙 _ :=
  pointedEnrichedMappingCylinderTarget_projection (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyLeftMap A r) (presentedPerfectDGKanAssemblyLeft_whisker A r) C

/-- 元の源比較と射影の合成は、元の同じ隣接段左脚。 -/
lemma presentedPerfectDGKanAssemblyCylinderSource_projection (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    presentedPerfectDGKanAssemblyCylinderSourceMap A r C ≫
      presentedPerfectDGKanAssemblyCylinderProjectionMap A r C =
        presentedPerfectDGKanAssemblyLeftMap A r C :=
  pointedEnrichedMappingCylinderSource_projection (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyLeftMap A r) (presentedPerfectDGKanAssemblyLeft_whisker A r) C

end SerrePositivity.KST.SConstruction
