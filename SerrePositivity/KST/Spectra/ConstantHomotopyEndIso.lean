module

public import SerrePositivity.KST.Spectra.ConstantWeightedNerveIso
public import SerrePositivity.KST.Spectra.ProductSectionsIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanSectionsIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SectionsFunctor

/-!
概要：定値図式の Bousfield–Kan end は底の nerve から係数への内部 Hom である。
方針：weighted nerve の切断、定値係数の直積同型、直積の切断の比較を合成する。
規約：単体集合の実際の同型。∞ 圏の極限性は使わない。
使われ方：Goerss–Jardine VIII §2。自明作用の hG を nerve からの写像空間で扱う。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (C : Type u) [SmallCategory C] (X : SSet.{u})

/-- 概要：定値 weighted nerve の直積同型は底上の同型となる。
方針：直積からの射が底の第一射影を被覆する式を使う。
規約：底は通常の圏 C の nerve。
使われ方：Goerss–Jardine VIII §2。定値図式の切断空間の比較。 -/
def constantWeightedNerveOverIso :
    Over.mk (fst (nerve C) X) ≅
      Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection ((Functor.const C).obj X)) :=
  Over.isoMk (constantWeightedNerveIso C X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantProduct_projection C X)

/-- 概要：定値図式の homotopy end と底の nerve からの写像空間の標準同型。
方針：切断表示へ移し、底上の直積同型を通じて直積の切断を同定する。
規約：C と係数 X に Kan 条件を要求しない。
使われ方：Goerss–Jardine VIII §2。自明作用の有理 Shapiro の写像空間模型。 -/
def constantHomotopyEndIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim ((Functor.const C).obj X) ≅ (ihom (nerve C)).obj X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsIso ((Functor.const C).obj X) ≪≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsFunctor (nerve C)).mapIso (constantWeightedNerveOverIso C X)).symm ≪≫
      productSectionsIso (nerve C) X

end

end SerrePositivity.KST.Spectra
