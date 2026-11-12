module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.EmptySimplicialDomain
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.FiniteHornUniverseIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.PointConeSpanIso

/-!
概要：有限交換の空形状と点 cospan を、小さい形状の宇宙持ち上げと同定する。
方針：空形状の始対象一意性と、ホーン・反転・点 span の元の全同型を合成する。
規約：形状の頂点と全単体を保つ厳密な同型を使う。
使われ方：I-2 d′ の有限極限保存の宇宙接続。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 小さい空部分複体の持ち上げは、任意の大きい空部分複体と同型。 -/
def finiteExchangeEmptyLiftIso (T : SSet.{u + 1}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (⊥ : (Δ[0] : SSet.{u}).Subcomplex) ≅
      (⊥ : T.Subcomplex) :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.uliftSSet_isInitial_of_isInitial Subcomplex.isInitialBot).uniqueUpToIso
    Subcomplex.isInitialBot

/-- 小さい cospan ホーンの持ち上げは、大きい点 span の反対形状と同型。 -/
def finiteExchangePointCospanLiftIso :
    (SSet.uliftFunctor.{u + 1, u}).obj (horn 2 2 : SSet.{u}) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpan.{u + 1}.op :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso 2 2 ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso 2 0 ≪≫
    (SSet.opFunctor.mapIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpanIso).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
