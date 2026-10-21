module

public import SerrePositivity.InfinityCategories.F2.RelativeCospanSections
public import SerrePositivity.InfinityCategories.F2.CoherentCospanNativeConeSections

/-!
概要：元の native 全錐の切断族を、左右二辺の切断の厳密な引き戻しへ送る。
方針：形状の押し出しによる表示同型を同じ切断族へ合成し、両射影の展開を計算する。
規約：元の全 pointed 錐と全パラメータを保持。使われ方：指定 path 付き模型比較への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection F) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (pullback f g) :=
  HomotopyLimits.kanComplex_of_iso (relativeCospanSectionsIso pointedSpaceProjection d)

/-- 元の全錐に由来する同じ族を、二辺上の切断の引き戻しへ表示する。 -/
def coherentCospanNativeSectionPullback : a ⟶ pullback f g :=
  coherentCospanNativeConeSections F X Y Z C b ≫
    (relativeCospanSectionsIso pointedSpaceProjection d).hom

/-- 左射影は元の全錐の左辺への制限そのもの。 -/
lemma coherentCospanNativeSectionPullback_left :
    coherentCospanNativeSectionPullback F X Y Z C b ≫ pullback.fst f g =
      coherentCospanNativeConeSections F X Y Z C b ≫
        relativeFunctorPre pointedSpaceProjection d horn₂₂.ι₀₂ := by
  rw [coherentCospanNativeSectionPullback, Category.assoc,
    relativeCospanSectionsIso_left pointedSpaceProjection d]

/-- 右射影は元の全錐の右辺への制限そのもの。 -/
lemma coherentCospanNativeSectionPullback_right :
    coherentCospanNativeSectionPullback F X Y Z C b ≫ pullback.snd f g =
      coherentCospanNativeConeSections F X Y Z C b ≫
        relativeFunctorPre pointedSpaceProjection d horn₂₂.ι₁₂ := by
  rw [coherentCospanNativeSectionPullback, Category.assoc,
    relativeCospanSectionsIso_right pointedSpaceProjection d]

/-- 左射影を展開すると元の全 pointed 錐の同じ左辺の全族になる。 -/
lemma coherentCospanNativeSectionPullback_left_uncurry :
    relativeFunctorUncurry
      (coherentCospanNativeSectionPullback F X Y Z C b ≫ pullback.fst f g) =
      (horn₂₂.ι₀₂ ▷ a) ≫ (joinInr Δ[0] (horn 2 2) ▷ a) ≫
        coherentCospanPointedConeLift F X Y Z C b := by
  rw [coherentCospanNativeSectionPullback_left]
  have he := relativeFunctorUncurry_pre (p := pointedSpaceProjection)
    (coherentCospanNativeConeSections F X Y Z C b) horn₂₂.ι₀₂
  rw [coherentCospanNativeConeSections_uncurry] at he
  exact he

/-- 右射影でも元の全 pointed 錐の同じ全族を回収する。 -/
lemma coherentCospanNativeSectionPullback_right_uncurry :
    relativeFunctorUncurry
      (coherentCospanNativeSectionPullback F X Y Z C b ≫ pullback.snd f g) =
      (horn₂₂.ι₁₂ ▷ a) ≫ (joinInr Δ[0] (horn 2 2) ▷ a) ≫
        coherentCospanPointedConeLift F X Y Z C b := by
  rw [coherentCospanNativeSectionPullback_right]
  have he := relativeFunctorUncurry_pre (p := pointedSpaceProjection)
    (coherentCospanNativeConeSections F X Y Z C b) horn₂₂.ι₁₂
  rw [coherentCospanNativeConeSections_uncurry] at he
  exact he

/-- 各点の元の錐の極限性から、二辺の切断の引き戻しへの実際の比較は同値。 -/
lemma coherentCospanNativeSectionPullback_isQCatEquivalence (hc : IsLimitCone c) :
    IsQCatEquivalence (coherentCospanNativeSectionPullback F X Y Z C b) :=
  (coherentCospanNativeConeSections_isQCatEquivalence F X Y Z C b hc).comp
    (qCatEquivalenceOfIso (relativeCospanSectionsIso pointedSpaceProjection d)).isQCatEquivalence

end SerrePositivity.InfinityCategories.F2
