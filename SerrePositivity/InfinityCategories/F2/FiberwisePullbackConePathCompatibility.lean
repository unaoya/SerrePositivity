module

public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackConeCompositeCompatibility

/-!
概要：全空間錐の指定可換性と元の二射影・path の整合。
方針：比較を通る射影を元の射影の Kan 置換へ厳密に輸送する。
規約：指定同型を保持。使われ方：coherent 余極限錐の引き戻し交換。
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

/-- 概要：元の全空間二射影の Kan 置換の間の指定 path 同型。
方針：元の区間 path を比較で引き戻し両端だけ輸送。
規約：指定 path の類。使われ方：全空間錐の可換性との比較。 -/
def fiberwisePullbackTotalPathIso :
    FunctorIso
      (continuousKanReplacement.map (fiberwiseIntervalPullbackLeft p f g) ≫ continuousKanMap f)
      (continuousKanReplacement.map (fiberwiseIntervalPullbackRight p f g) ≫ continuousKanMap g) :=
  functorIsoOfEq
    ((intervalPullbackPathIso (continuousKanMap f) (continuousKanMap g)).precomp
      (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
        (fiberwisePullbackTargetKanObject f g).obj from fiberwisePullbackComparisonKanMap p f g))
    (congrArg (fun k => k ≫ continuousKanMap f) (fiberwisePullbackConeLeftComposite_target p f g))
    (congrArg (fun k => k ≫ continuousKanMap g) (fiberwisePullbackConeRightComposite_target p f g))

/-- 概要：正規化した path 同型は元の指定同型と型を含めて一致。
方針：両端だけの輸送。規約：指定値。使われ方：元の全円柱の回収。 -/
lemma fiberwisePullbackTotalPathIso_heq :
    HEq (fiberwisePullbackTotalPathIso p f g)
      ((intervalPullbackPathIso (continuousKanMap f) (continuousKanMap g)).precomp
        (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
          (fiberwisePullbackTargetKanObject f g).obj from
            fiberwisePullbackComparisonKanMap p f g)) :=
  functorIsoOfEq_heq _ _ _

/-- 概要：元の二射影への指定脚比較と指定 path は native 可換性と整合する。
方針：合成比較の整合を終点の厳密な等式だけで輸送。
規約：元の比較同型の等式。使われ方：coherent 引き戻し交換の可換性。 -/
lemma fiberwisePullbackCone_projection_commutativity :
    (fiberwisePullbackConeFstIso p f g).postcomp (continuousKanMap f) ≪≫
        fiberwisePullbackTotalPathIso p f g =
      fiberwisePullbackConeNativeCommutativity p f g ≪≫
        (fiberwisePullbackConeSndIso p f g).postcomp (continuousKanMap g) := by
  apply cospanFunctorIso_target_transport
    (continuousKanMap f) (continuousKanMap g)
    (fiberwisePullbackConeLeftCompositeIso p f g)
    (fiberwisePullbackConeRightCompositeIso p f g)
    (fiberwisePullbackConeFstIso p f g) (fiberwisePullbackConeSndIso p f g)
    (fiberwisePullbackConeNativeCommutativity p f g)
    ((intervalPullbackPathIso (continuousKanMap f) (continuousKanMap g)).precomp
      (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
        (fiberwisePullbackTargetKanObject f g).obj from fiberwisePullbackComparisonKanMap p f g))
    (fiberwisePullbackTotalPathIso p f g)
    (fiberwisePullbackConeLeftComposite_target p f g)
    (fiberwisePullbackConeRightComposite_target p f g)
    (functorIsoOfEq_heq _ _ _) (functorIsoOfEq_heq _ _ _) (functorIsoOfEq_heq _ _ _)
    (fiberwisePullbackConeComposite_projection_commutativity p f g)

end SerrePositivity.InfinityCategories.F2
