module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverContractible
public import SerrePositivity.EInfinity.Hammock.ValueSupportWeak

/-!
# 元の自由圏の全指定 hammock の評価の弱同値性

概要：元の hammock から自由 groupoid の離散な Hom への評価自身は弱同値。
方針：元の自由被覆の各 fiber の弱可縮性と値の有限支持による判定を使う。
規約：モデル構造、木性、fiber の可縮性を追加入力にしない。
使われ方：DK の自由積分解と右比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory SerrePositivity.InfinityCategories

lemma hammockValue_isWeakHomotopyEquivalence {Q : Type u} [Quiver.{v} Q]
    (A : Q) (Y : Paths Q) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (hammockValue A Y) :=
  ValueSupport.weak_of_contractible_fibers _ (hammockValueFiber_isWeaklyContractible A Y)

lemma existingHammockValue_isWeakHomotopyEquivalence {Q : Type u} [Quiver.{u} Q]
    (A : Q) (Y : Paths Q) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (Zigzag.Value.colimitValue _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top
        ((Paths.of Q).obj A) Y) :=
  ValueSupport.weak_of_contractible_fibers _
    (existingHammockValueFiber_isWeaklyContractible A Y)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
