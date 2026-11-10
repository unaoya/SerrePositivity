module

public import SerrePositivity.KST.Comparison.HomotopyPullbackThreeInputs

/-!
# Ex∞ によるホモトピー引き戻しの保存・反映

概要：Ex∞ は、構成した模型によるホモトピー引き戻し性を保存・反映する。
方針：四角形の四つの頂点を単位で比較し、全ての頂点の局所化同型による不変性を適用する。
規約：Segal 1974 Proposition 1.6 の貼り合わせの Kan 置換への還元。
使われ方：任意の四角形を Kan 複体の四角形に置き換える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：四角形がホモトピー引き戻しであることは、Ex∞ で送った四角形の同じ性質と同値である。
方針：単位の自然性を四つの面の可換条件に使い、四つの頂点の局所化可逆性を適用する。
規約：単位の anodyne 性、Ex∞ の有限極限・Kan fibration 保存は既証のものを使う。
使われ方：Segal の貼り合わせで Kan な入力へ移る。
-/
theorem isHomotopyPullback_exInfinity_iff {P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} (sq : CommSq a b f g) :
    IsHomotopyPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_commSq sq) ↔ IsHomotopyPullback sq := by
  symm
  exact isHomotopyPullback_iff_of_localized_isIso sq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_commSq sq)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app P) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app B)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality g)
    inferInstance inferInstance inferInstance inferInstance

end SerrePositivity.KST.Comparison
