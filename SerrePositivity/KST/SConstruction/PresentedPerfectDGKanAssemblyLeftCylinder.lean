module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblySpan
public import SerrePositivity.KST.SConstruction.PointedEnrichedMappingCylinder

/-! # 元の隣接段左脚の同じ実写像円柱への厳密 dg 豊穣関手
概要：元の Kan 隣接段 span の左脚を、同じ点つき実写像円柱に置き換える。
方針：元の全 Hom 自然性を、実円柱と実押し出しの厳密豊穣関手に入力する。
規約：単射性・弱同値性はここでは仮定しない。使われ方：BF の homotopy pushout 段。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の左脚の同じ実写像円柱を値とする、全厳密 dg 入力上の厳密豊穣関手。 -/
def presentedPerfectDGKanAssemblyLeftCylinderFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  pointedEnrichedMappingCylinderFunctor
    (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyLeftMap A r) (presentedPerfectDGKanAssemblyLeft_whisker A r)

/-- 実値は、元の同じ左脚の点つき押し出し写像円柱そのもの。 -/
lemma presentedPerfectDGKanAssemblyLeftCylinderFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj C).obj =
      pointedTensorMappingCylinder
        (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
          ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
            presentedPerfectDGKanAssemblyLeftMap A r C) := rfl

end SerrePositivity.KST.SConstruction
