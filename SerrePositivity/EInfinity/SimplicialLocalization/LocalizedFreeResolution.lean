module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolution
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.StrictLocalization

/-!
# 自由単体的相対圏の次数ごとの厳密な局所化

概要：Dwyer–Kan の自由解像を全単体作用素に沿って次数ごとに局所化する。
方針：自由相対圏の全単体的解像に厳密な局所化関手を後合成する。
規約：各次数の指定矢は元の弱同値だけからなる列。
使われ方：固定対象を持つ単体的圏とその Kan 化の構成。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory

/-- 概要：全自由次数の指定矢を反転した単体的な圏の図式（Dwyer–Kan）。
方針：同じ全単体的相対解像へ構成的な厳密な局所化を後合成する。
規約：通常の単体圏上の実際の関手で、全恒等式を保持する。
使われ方：単体的局所化の固定対象の Hom の構成。 -/
def localizedFreeResolution (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) : SimplicialObject Cat.{u, u} :=
  freeResolution C ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor

/-- 概要：局所化した自由解像から元の普通の局所化への augmentation（Dwyer–Kan）。
方針：同じ全 augmentation を厳密な局所化関手で送る。
規約：全単体作用素と元の射の反転を保持する。
使われ方：DK 比較の π₀ と普通の局所化 Hom の接続。 -/
def localizedFreeResolutionAugmentation (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    localizedFreeResolution C ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (Cat.of C.weakEquivalences.Localization) :=
  Functor.whiskerRight (freeResolutionAugmentationNatTrans C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor ≫
    (Functor.constComp SimplexCategoryᵒᵖ C _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationFunctor).hom

end SerrePositivity.EInfinity.SimplicialLocalization
