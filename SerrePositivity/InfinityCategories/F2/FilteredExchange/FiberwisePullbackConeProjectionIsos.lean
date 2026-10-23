module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackConeNativeCommutativity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanIntervalConePathCompatibility

/-!
概要：全空間錐の元の二脚を元の具体的な二射影へ指定同型で比較する。
方針：全錐の指定比較と区間錐の指定射影比較を合成する。
規約：元の全空間頂点と比較射を保持。使われ方：元の全 path と余極限錐の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
  [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]

/-- 概要：全空間錐の左脚から元の比較の第一射影への指定同型。
方針：同じ全錐円柱と区間錐の比較を合成。規約：指定値。使われ方：元の射影の回収。 -/
def fiberwisePullbackConeLeftCompositeIso :
    FunctorIso (fiberwisePullbackNativeConeKanLeg p f g (AsSmall.up.obj WalkingCospan.left))
      (fiberwisePullbackComparisonKanMap p f g ≫
        intervalPullbackLeft (continuousKanMap f) (continuousKanMap g)) :=
  fiberwisePullbackConeLegIso p f g (AsSmall.up.obj WalkingCospan.left) ≪≫
    (intervalPullbackConeFstIso (continuousKanMap f) (continuousKanMap g)).precomp
      (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
        (fiberwisePullbackTargetKanObject f g).obj from fiberwisePullbackComparisonKanMap p f g)

/-- 概要：全空間錐の右脚から元の比較の第二射影への指定同型。
方針：同じ全錐円柱と区間錐の比較を合成。規約：指定値。使われ方：元の射影の回収。 -/
def fiberwisePullbackConeRightCompositeIso :
    FunctorIso (fiberwisePullbackNativeConeKanLeg p f g (AsSmall.up.obj WalkingCospan.right))
      (fiberwisePullbackComparisonKanMap p f g ≫
        intervalPullbackRight (continuousKanMap f) (continuousKanMap g)) :=
  fiberwisePullbackConeLegIso p f g (AsSmall.up.obj WalkingCospan.right) ≪≫
    (intervalPullbackConeSndIso (continuousKanMap f) (continuousKanMap g)).precomp
      (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
        (fiberwisePullbackTargetKanObject f g).obj from fiberwisePullbackComparisonKanMap p f g)

/-- 概要：比較を通る第一射影は元の全空間射影の Kan 置換そのもの。
方針：元の比較の厳密な座標式。規約：射の等式。使われ方：終点の正規化。 -/
lemma fiberwisePullbackConeLeftComposite_target :
    fiberwisePullbackComparisonKanMap p f g ≫
      intervalPullbackLeft (continuousKanMap f) (continuousKanMap g) =
        continuousKanReplacement.map (fiberwiseIntervalPullbackLeft p f g) := by
  change fiberwisePullbackKanComparison p f g ≫ _ ≫ _ = _
  exact fiberwisePullbackKanComparison_left p f g

/-- 概要：比較を通る第二射影は元の全空間射影の Kan 置換そのもの。
方針：元の比較の厳密な座標式。規約：射の等式。使われ方：終点の正規化。 -/
lemma fiberwisePullbackConeRightComposite_target :
    fiberwisePullbackComparisonKanMap p f g ≫
      intervalPullbackRight (continuousKanMap f) (continuousKanMap g) =
        continuousKanReplacement.map (fiberwiseIntervalPullbackRight p f g) :=
  fiberwisePullbackKanComparison_right p f g

/-- 概要：元の第一射影の Kan 置換への指定比較。
方針：終点の厳密な式だけ輸送。規約：指定値。使われ方：余極限錐の第一脚。 -/
def fiberwisePullbackConeFstIso :
    FunctorIso (fiberwisePullbackNativeConeKanLeg p f g (AsSmall.up.obj WalkingCospan.left))
      (continuousKanReplacement.map (fiberwiseIntervalPullbackLeft p f g)) :=
  functorIsoOfEq (fiberwisePullbackConeLeftCompositeIso p f g) rfl
    (fiberwisePullbackConeLeftComposite_target p f g)

/-- 概要：元の第二射影の Kan 置換への指定比較。
方針：終点の厳密な式だけ輸送。規約：指定値。使われ方：余極限錐の第二脚。 -/
def fiberwisePullbackConeSndIso :
    FunctorIso (fiberwisePullbackNativeConeKanLeg p f g (AsSmall.up.obj WalkingCospan.right))
      (continuousKanReplacement.map (fiberwiseIntervalPullbackRight p f g)) :=
  functorIsoOfEq (fiberwisePullbackConeRightCompositeIso p f g) rfl
    (fiberwisePullbackConeRightComposite_target p f g)

end SerrePositivity.InfinityCategories.F2
