module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwisePullbackConeLegNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeNativeCommutativity
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CospanIsoCancellation

/-!
概要：元の全空間錐と区間錐の native な可換性の指定比較。
方針：二つの脚の自然性から共通の中心比較を消去する。
規約：元の比較射と左右の指定同型を保持。使われ方：元の path と全空間錐の接続。
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

/-- 概要：元の全空間錐の左右の二単体からの指定可換同型。
方針：中心脚を消去。規約：元の二単体の値。使われ方：元の path への比較。 -/
def fiberwisePullbackConeNativeCommutativity :
    FunctorIso (fiberwisePullbackNativeConeKanLeg p f g (AsSmall.up.obj WalkingCospan.left) ≫
      continuousKanMap f)
      (fiberwisePullbackNativeConeKanLeg p f g (AsSmall.up.obj WalkingCospan.right) ≫
        continuousKanMap g) :=
  (fiberwisePullbackConeTriangleIso p f g (AsSmall.up.map WalkingCospan.Hom.inl)).symm ≪≫
    fiberwisePullbackConeTriangleIso p f g (AsSmall.up.map WalkingCospan.Hom.inr)

/-- 概要：元の二脚の指定比較は全空間錐と区間錐の native な可換性に対して整合。
方針：二つの正規化した自然性の式から中心比較を消去。
規約：指定同型の値の等式。使われ方：元の区間 path との最終照合。 -/
lemma fiberwisePullbackConeNativeCommutativity_comparison :
    fiberwisePullbackConeNativeCommutativity p f g ≪≫
        (fiberwisePullbackConeLegIso p f g (AsSmall.up.obj WalkingCospan.right)).postcomp
          (continuousKanMap g) =
      (fiberwisePullbackConeLegIso p f g (AsSmall.up.obj WalkingCospan.left)).postcomp
          (continuousKanMap f) ≪≫
        (intervalPullbackConeNativeCommutativity (continuousKanMap f) (continuousKanMap g)).precomp
          (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
            (fiberwisePullbackTargetKanObject f g).obj from
              fiberwisePullbackComparisonKanMap p f g) := by
  have h := cospanIso_cancel
    (fiberwisePullbackConeTriangleIso p f g (AsSmall.up.map WalkingCospan.Hom.inl))
    (fiberwisePullbackConeTriangleIso p f g (AsSmall.up.map WalkingCospan.Hom.inr))
    ((fiberwisePullbackConeLegIso p f g (AsSmall.up.obj WalkingCospan.left)).postcomp
      (continuousKanMap f))
    ((fiberwisePullbackConeLegIso p f g (AsSmall.up.obj WalkingCospan.right)).postcomp
      (continuousKanMap g))
    (fiberwisePullbackConeLegIso p f g (AsSmall.up.obj WalkingCospan.one))
    ((intervalPullbackConeTriangleIso (continuousKanMap f) (continuousKanMap g)
      (AsSmall.up.map WalkingCospan.Hom.inl)).precomp
        (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
          (fiberwisePullbackTargetKanObject f g).obj from fiberwisePullbackComparisonKanMap p f g))
    ((intervalPullbackConeTriangleIso (continuousKanMap f) (continuousKanMap g)
      (AsSmall.up.map WalkingCospan.Hom.inr)).precomp
        (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
          (fiberwisePullbackTargetKanObject f g).obj from fiberwisePullbackComparisonKanMap p f g))
    (fiberwisePullbackConeLegIso_naturality p f g (AsSmall.up.map WalkingCospan.Hom.inl))
    (fiberwisePullbackConeLegIso_naturality p f g (AsSmall.up.map WalkingCospan.Hom.inr))
  simpa only [fiberwisePullbackConeNativeCommutativity, intervalPullbackConeNativeCommutativity,
    functorIso_precomp_trans, functorIso_precomp_symm, Iso.trans_assoc] using h

end SerrePositivity.InfinityCategories.F2
