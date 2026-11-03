module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalKanComparison
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalKanCoordinates
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram

/-!
概要：fiber ごとの path 引き戻しの全空間 Kan 模型から、元の Kan cospan の path 引き戻しへの比較。
方針：path の Kan 比較の両端の厳密な一致で、元の二つの入力を順に引き戻す。
規約：比較は元の二射と選んだ path 比較を保持する。
使われ方：一般 coherent な cospan の filtered 余極限と引き戻しの交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：第一入力と元の path の Kan 比較を、Kan cospan の第一段へ入れる。
方針：path の始点の厳密な式を使って引き戻しへ持ち上げる。
規約：元の第一射 f の Kan 置換。使われ方：全比較の第一段。 -/
def fiberwisePullbackKanReplacementComparison :
    continuousKanReplacement.obj (fiberwiseIntervalPullback p f g) ⟶
      intervalReplacement (continuousKanReplacement.map f) :=
  pullback.lift
    (continuousKanReplacement.map (fiberwiseIntervalPullbackPath p f g) ≫
      fiberwiseIntervalKanComparison p)
    (continuousKanReplacement.map (fiberwiseIntervalPullbackLeft p f g)) (by
      rw [Category.assoc, fiberwiseIntervalKanComparison_endpoint,
        ← CategoryTheory.Functor.map_comp, fiberwiseIntervalPullbackPath_zero,
        CategoryTheory.Functor.map_comp])

/-- 概要：第一段の終点は元の第二入力の像の Kan 置換。
方針：path 比較の終点と元の引き戻しの終点条件を計算する。
規約：元の第二射 g。使われ方：第二段への厳密な持ち上げ。 -/
lemma fiberwisePullbackKanReplacementComparison_endpoint :
    fiberwisePullbackKanReplacementComparison p f g ≫
      intervalReplacementEndpoint (continuousKanReplacement.map f) =
        continuousKanReplacement.map (fiberwiseIntervalPullbackRight p f g) ≫
          continuousKanReplacement.map g := by
  change fiberwisePullbackKanReplacementComparison p f g ≫
    (pullback.fst ((intervalEndpointNatTrans 0).app (continuousKanReplacement.obj H))
      (continuousKanReplacement.map f) ≫
        (intervalEndpointNatTrans 1).app (continuousKanReplacement.obj H)) = _
  rw [← Category.assoc, fiberwisePullbackKanReplacementComparison, pullback.lift_fst,
    Category.assoc, fiberwiseIntervalKanComparison_endpoint,
    ← CategoryTheory.Functor.map_comp, fiberwiseIntervalPullbackPath_one,
    CategoryTheory.Functor.map_comp]

/-- 概要：元の fiber ごとの path 引き戻しから、Kan 模型の cospan の引き戻しへの実際の比較。
方針：第一段の終点式で第二入力の Kan 射影を引き戻す。
規約：元の三つの全空間を各 Kan 模型へ写す。使われ方：filtered 引き戻し交換の比較射。 -/
def fiberwisePullbackKanComparison :
    continuousKanReplacement.obj (fiberwiseIntervalPullback p f g) ⟶
      intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g) :=
  pullback.lift (fiberwisePullbackKanReplacementComparison p f g)
    (continuousKanReplacement.map (fiberwiseIntervalPullbackRight p f g))
    (fiberwisePullbackKanReplacementComparison_endpoint p f g)

end SerrePositivity.InfinityCategories.F2
