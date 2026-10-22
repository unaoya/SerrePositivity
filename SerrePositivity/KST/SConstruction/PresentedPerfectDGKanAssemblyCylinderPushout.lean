module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderWhisker
public import SerrePositivity.KST.SConstruction.PointedSpanPushoutEnrichedFunctor

/-! # 元の隣接段 span の左脚を実写像円柱に置換した押し出し
概要：同じ元の右脚を保ち、左脚の実円柱源比較で実 span と押し出しを構成する。
方針：元の全 Hom 自然性を標準 end に束ね、実押し出しの厳密豊穣関手を適用する。
規約：弱同値性・単射性の未証明の結論は使わない。使われ方：BF 帰納段の候補。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の同じ右脚を保持し、左脚を実写像円柱源比較にした厳密豊穣 span。 -/
def presentedPerfectDGKanAssemblyCylinderSpanFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSpanDiagram.{max (u + 1) v} :=
  pointedEnrichedSpanFunctor
    (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGKanAssemblyCylinderSourceMap A r)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGKanAssemblyCylinderSource_whisker A r)
    (presentedPerfectDGKanAssemblyRight_whisker A r)

/-- 同じ元の右脚と実写像円柱からの、実押し出し値の厳密豊穣関手。 -/
def presentedPerfectDGKanAssemblyCylinderPushoutFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  (presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).comp SSet
    pointedSpanPushoutEnrichedFunctor

/-- 実値は、同じ元の右脚と同じ実写像円柱源射の点つき押し出しそのもの。 -/
lemma presentedPerfectDGKanAssemblyCylinderPushoutFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj =
      pushout
        (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
          ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C).obj from
            presentedPerfectDGKanAssemblyCylinderSourceMap A r C)
        (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
          ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj from
            presentedPerfectDGKanAssemblyRightMap A r C) := rfl

end SerrePositivity.KST.SConstruction
