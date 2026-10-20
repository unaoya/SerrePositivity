module

public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackConeProjectionIsos
public import SerrePositivity.InfinityCategories.F2.CospanFunctorIsoComposition

/-!
概要：元の全空間錐の両脚の指定合成比較と元の引き戻し path の整合。
方針：二段の cospan 比較を同じ指定値のまま合成する。
規約：頂点・比較射を変更しない。使われ方：具体的な全空間射影と余極限錐の接続。
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

/-- 概要：全空間錐の指定脚比較を通る元の path は元の native 可換性に整合。
方針：全錐比較と区間錐の元の path の整合を合成。
規約：元の指定値の等式。使われ方：元の全 path との比較。 -/
lemma fiberwisePullbackConeComposite_projection_commutativity :
    (fiberwisePullbackConeLeftCompositeIso p f g).postcomp (continuousKanMap f) ≪≫
        (intervalPullbackPathIso (continuousKanMap f) (continuousKanMap g)).precomp
          (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
            (fiberwisePullbackTargetKanObject f g).obj from
              fiberwisePullbackComparisonKanMap p f g) =
      fiberwisePullbackConeNativeCommutativity p f g ≪≫
        (fiberwisePullbackConeRightCompositeIso p f g).postcomp (continuousKanMap g) :=
  cospanFunctorIso_compose
    (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
      (fiberwisePullbackTargetKanObject f g).obj from fiberwisePullbackComparisonKanMap p f g)
    (continuousKanMap f) (continuousKanMap g)
    (fiberwisePullbackConeLegIso p f g (AsSmall.up.obj WalkingCospan.left))
    (fiberwisePullbackConeLegIso p f g (AsSmall.up.obj WalkingCospan.right))
    (intervalPullbackConeFstIso (continuousKanMap f) (continuousKanMap g))
    (intervalPullbackConeSndIso (continuousKanMap f) (continuousKanMap g))
    (fiberwisePullbackConeNativeCommutativity p f g)
    (intervalPullbackConeNativeCommutativity (continuousKanMap f) (continuousKanMap g))
    (intervalPullbackPathIso (continuousKanMap f) (continuousKanMap g))
    (fiberwisePullbackConeNativeCommutativity_comparison p f g)
    (intervalPullbackCone_projection_commutativity (continuousKanMap f) (continuousKanMap g))

end SerrePositivity.InfinityCategories.F2
