module

public import SerrePositivity.InfinityCategories.Simplicial.EmptySimplicialDomain
public import SerrePositivity.InfinityCategories.F1.Simplicial.FiniteHornUniverseIso
public import SerrePositivity.InfinityCategories.F1.Joins.PointConeSpanIso

/-!
概要：有限交換の空形状と点 cospan を、小さい形状の宇宙持ち上げと同定する。
方針：空形状の始対象一意性と、ホーン・反転・点 span の元の全同型を合成する。
規約：形状の頂点と全単体を保つ厳密な同型を使う。
使われ方：I-2 d′ の有限極限保存の宇宙接続。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 小さい空部分複体の持ち上げは、任意の大きい空部分複体と同型。 -/
def finiteExchangeEmptyLiftIso (T : SSet.{u + 1}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (⊥ : (Δ[0] : SSet.{u}).Subcomplex) ≅
      (⊥ : T.Subcomplex) :=
  (uliftSSet_isInitial_of_isInitial Subcomplex.isInitialBot).uniqueUpToIso
    Subcomplex.isInitialBot

/-- 小さい cospan ホーンの持ち上げは、大きい点 span の反対形状と同型。 -/
def finiteExchangePointCospanLiftIso :
    (SSet.uliftFunctor.{u + 1, u}).obj (horn 2 2 : SSet.{u}) ≅ pointConeSpan.{u + 1}.op :=
  uliftHornIso 2 2 ≪≫ hornReverseIso 2 0 ≪≫
    (SSet.opFunctor.mapIso pointConeSpanIso).symm

end SerrePositivity.InfinityCategories.F2.Ind
