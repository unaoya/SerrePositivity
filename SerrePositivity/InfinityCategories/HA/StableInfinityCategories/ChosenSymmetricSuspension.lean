module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricSuspension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSwapChoice

/-! # 各頂点で選ぶ対称な suspension 模型

概要：安定 ∞ 圏の任意の頂点で、転置前後の span が厳密に等しい suspension を選べる。
方針：選んだ零対象への辺を一つ選び、それを二枝に使う。
規約：従来の suspension 関手の選択は変更しない。使われ方：交換の符号を対称模型で証明するための帰着。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories


/-- 概要：指定頂点から同じ零対象への同じ辺を二枝に使う suspension を選ぶ。
方針：零対象への辺を選び、対称な suspension の構成を使う。
規約：既存の chosenSuspensionSquare とは別の補助的な選択。使われ方：二枝交換のループ表示。 -/
def chosenSymmetricSuspensionSquare {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricSuspensionSquare (Classical.choice ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).isTerminal.nonempty_edge x))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).isZero

/-- 概要：選んだ対称な suspension は転置しても入力 span が変わらない。
方針：同じ辺を二度使う構成の span の等号を適用する。
規約：追加の span の等号を仮定しない。使われ方：同じ coslice 内での交換の比較。 -/
lemma chosenSymmetricSuspensionSquare_sameSpan {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (chosenSymmetricSuspensionSquare x).transpose.square =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (chosenSymmetricSuspensionSquare x).square :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricSuspensionSquare_sameSpan _ _

/-- 概要：選んだ対称な suspension の交換同型は同じ span 上の標準余極限頂点比較である。
方針：構成済みの span の等号を前段の条件付きの比較に与える。
規約：安定性のみから得られ、span の等号を追加仮定しない。使われ方：交換作用の Hom 表示。 -/
lemma chosenSymmetricSuspensionSquare_swap_comparison
    {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (x : X _⦋0⦌) :
    (Arrow.mk (chosenSymmetricSuspensionSquare x).swapIso.hom : Arrow (hoFunctor.obj X)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (chosenSymmetricSuspensionSquare x).square)
        ((chosenSymmetricSuspensionSquare x).transposedCoconeOfSameSpan
          (chosenSymmetricSuspensionSquare_sameSpan x))
        (chosenSymmetricSuspensionSquare x).isPushout
        ((chosenSymmetricSuspensionSquare x).transposedCoconeOfSameSpan_isColimit
          (chosenSymmetricSuspensionSquare_sameSpan x))).hom :=
  (chosenSymmetricSuspensionSquare x).swapIso_eq_colimitVertexIso_arrow_of_sameSpan
    (chosenSymmetricSuspensionSquare_sameSpan x)

section
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
local instance : Preadditive X.HomotopyCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho (X := X)

/-- 概要：対称模型で交換の符号を証明すれば任意の suspension の交換の符号が従う。
方針：標準比較を介した負の恒等射の転送を使う。
規約：対称模型の符号は仮定であり、ここではまだ証明しない。使われ方：一般の選択への帰着。 -/
lemma SuspensionSquare.swapIso_eq_neg_id_of_chosenSymmetric
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x)
    (h : (chosenSymmetricSuspensionSquare x).swapIso.hom =
      -𝟙 (SSet.HomotopyCategory.mk (chosenSymmetricSuspensionSquare x).vertex : hoFunctor.obj X)) :
    s.swapIso.hom = -𝟙 (SSet.HomotopyCategory.mk s.vertex : hoFunctor.obj X) :=
  s.swapIso_eq_neg_id_of_comparison (chosenSymmetricSuspensionSquare x) h

end

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
