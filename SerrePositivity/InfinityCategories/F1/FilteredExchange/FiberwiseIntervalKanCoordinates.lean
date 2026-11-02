module

public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConstantDiagram
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalKanComparison
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram

/-!
概要：選んだ Kan path 比較の、元の path 全体と二つの端点の厳密な一致。
方針：指定可換四角形の持ち上げの両三角形を読む。
規約：選択した比較射そのものを追跡する。
使われ方：二入力を保つ一般 coherent な引き戻し比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

private instance comparisonLifting {E B : SSet.{u}} (p : E ⟶ B) :
    HasLiftingProperty (continuousKanReplacementUnit.app (fiberwiseFunctorSpace p Δ[1]))
      (arrowEndpointPair (continuousKanReplacement.obj E)) :=
  continuousKanReplacementUnit_anodyne (fiberwiseFunctorSpace p Δ[1]) _
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)

/-- 概要：比較の単位への制限は元の path を全空間の単位で写した射そのもの。
方針：持ち上げの左三角形を読む。
規約：全 path 座標。使われ方：元の fiber の指定 path の保持。 -/
lemma fiberwiseIntervalKanComparison_unit {E B : SSet.{u}} (p : E ⟶ B) :
    continuousKanReplacementUnit.app (fiberwiseFunctorSpace p Δ[1]) ≫
      fiberwiseIntervalKanComparison p =
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) ≫
          (ihom (Δ[1] : SSet.{u})).map (continuousKanReplacementUnit.app E) :=
  (fiberwiseIntervalKanComparisonSquare p).fac_left

/-- 概要：比較の両端は元の二評価の Kan 置換の組。
方針：持ち上げの右三角形を読む。
規約：二端点を同時に固定。使われ方：比較射を指定した cospan へ制限する。 -/
lemma fiberwiseIntervalKanComparison_boundary {E B : SSet.{u}} (p : E ⟶ B) :
    fiberwiseIntervalKanComparison p ≫ arrowEndpointPair (continuousKanReplacement.obj E) =
      lift (continuousKanReplacement.map (fiberwiseIntervalEndpoint p 0))
        (continuousKanReplacement.map (fiberwiseIntervalEndpoint p 1)) :=
  (fiberwiseIntervalKanComparisonSquare p).fac_right

/-- 概要：比較は各指定端点の元の評価の Kan 置換に厳密に重なる。
方針：両端の式を第一・第二射影で読む。
規約：0 は始点、1 は終点。使われ方：二段の引き戻しの厳密な比較。 -/
lemma fiberwiseIntervalKanComparison_endpoint {E B : SSet.{u}} (p : E ⟶ B) (e : Fin 2) :
    fiberwiseIntervalKanComparison p ≫
      (intervalEndpointNatTrans e).app (continuousKanReplacement.obj E) =
        continuousKanReplacement.map (fiberwiseIntervalEndpoint p e) := by
  fin_cases e
  · change fiberwiseIntervalKanComparison p ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        continuousKanReplacement.map (fiberwiseIntervalEndpoint p 0)
    have h := congrArg (fun r ↦ r ≫ fst (continuousKanReplacement.obj E)
      (continuousKanReplacement.obj E)) (fiberwiseIntervalKanComparison_boundary p)
    simpa only [arrowEndpointPair, intervalEndpointNatTrans, Category.assoc, lift_fst] using h
  · change fiberwiseIntervalKanComparison p ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        continuousKanReplacement.map (fiberwiseIntervalEndpoint p 1)
    have h := congrArg (fun r ↦ r ≫ snd (continuousKanReplacement.obj E)
      (continuousKanReplacement.obj E)) (fiberwiseIntervalKanComparison_boundary p)
    simpa only [arrowEndpointPair, intervalEndpointNatTrans, Category.assoc, lift_snd] using h

end SerrePositivity.InfinityCategories.F2
