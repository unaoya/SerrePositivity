module

public import SerrePositivity.EInfinity.FrameHom.ComonadResolutionMap
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolution

/-!
# 自由相対圏の全解像の係数関手性

概要：Dwyer–Kan の自由解像に相対関手を全次数で送る。
方針：一般の comonad 解像の係数自然性へ同じ自由 comonad を代入する。
規約：元の解像・全作用素・augmentation を保持する。
使われ方：単体的局所化の係数関手の構成。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory
open FrameHom.ComonadResolution

/-- 概要：相対関手を元の自由解像の間の自然変換へ送る（Dwyer–Kan）。
方針：同じ自由 comonad の全解像の係数射を使う。
規約：全単体作用素との自然性を含む。
使われ方：局所化前の係数関手。 -/
def freeResolutionMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    freeResolution C ⟶ freeResolution D := resolutionMap _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad F

/-- 概要：自由解像は相対圏に関して関手をなす（Dwyer–Kan）。
方針：同じ comonad 解像の厳密な恒等・合成則を使う。
規約：係数と単体作用素の両方を保持する。
使われ方：厳密な次数ごとの局所化への後合成。 -/
def freeResolutionFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} ⥤ SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} where
  obj := freeResolution
  map := freeResolutionMap
  map_id := resolutionMap_id _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad
  map_comp := resolutionMap_comp _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad

/-- 概要：自由解像の係数射は元の augmentation と両立する（Dwyer–Kan）。
方針：同じ汎用 augmentation の係数自然性を使う。
規約：元の相対関手への比較の厳密な等式。
使われ方：局所化した自由解像の対象表示の保存。 -/
lemma freeResolutionMap_augmentation {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    freeResolutionMap F ≫ freeResolutionAugmentationNatTrans D =
      freeResolutionAugmentationNatTrans C ≫ (Functor.const SimplexCategoryᵒᵖ).map F :=
  resolutionMap_augmentation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad F

end SerrePositivity.EInfinity.SimplicialLocalization
