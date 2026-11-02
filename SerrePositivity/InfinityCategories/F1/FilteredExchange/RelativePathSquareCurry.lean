module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConstantDiagram
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanUnit
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.PathSquareCurry

/-!
概要：指定部分上の元の path 正方形を、実際の Kan 比較の全 path 座標として回収する。
方針：uncurry の単射性と元の単位上の path 比較式を使う。
規約：元の境界輸送の全円柱を保持。使われ方：引き戻し内の相対比較の厳密な制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の境界円柱の path 正方形を保てば curry 後の path 座標も厳密に一致。
方針：uncurry して積の並べ替えを戻す。規約：全単体。使われ方：相対比較の第三座標。 -/
lemma relativePathSquareCurry_restrict {K A E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (i : A ⟶ K)
    (L : A ⊗ (Δ[1] : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g)
    (F : ((Δ[1] : SSet.{u}) ⊗ K) ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj H)
    (hF : (((Δ[1] : SSet.{u}) ◁ i) ▷ (Δ[1] : SSet.{u})) ≫ F =
      (α_ (Δ[1] : SSet.{u}) A (Δ[1] : SSet.{u})).hom ≫
        fiberwisePullbackPathPrism p f g L ≫ continuousKanReplacementUnit.app H) :
    (i ▷ (Δ[1] : SSet.{u})) ≫ pathSquareCurry
      (((β_ K (Δ[1] : SSet.{u})).hom ▷ (Δ[1] : SSet.{u})) ≫ F) =
        L ≫ continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
          fiberwisePullbackKanComparison p f g ≫
            intervalPullbackPath (continuousKanReplacement.map f)
              (continuousKanReplacement.map g) := by
  have hu : continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
      fiberwisePullbackKanComparison p f g ≫ intervalPullbackPath
        (continuousKanReplacement.map f) (continuousKanReplacement.map g) =
      fiberwiseIntervalPullbackPath p f g ≫
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) ≫
          (ihom (Δ[1] : SSet.{u})).map (continuousKanReplacementUnit.app H) := by
    simpa only [intervalPullbackPath, Category.assoc] using
      fiberwisePullbackKanComparison_unit_path p f g
  rw [hu]
  apply uncurry_injective
  rw [uncurry_natural_left, pathSquareCurry, uncurry_curry]
  change _ = uncurry ((L ≫ fiberwiseIntervalPullbackPath p f g ≫
    pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B)) ≫
      (ihom (Δ[1] : SSet.{u})).map (continuousKanReplacementUnit.app H))
  rw [uncurry_natural_right]
  change (α_ (Δ[1] : SSet.{u}) A (Δ[1] : SSet.{u})).inv ≫
    ((((Δ[1] : SSet.{u}) ◁ i) ▷ (Δ[1] : SSet.{u})) ≫ F) =
      fiberwisePullbackPathPrism p f g L ≫ continuousKanReplacementUnit.app H
  rw [hF]
  simp only [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2
