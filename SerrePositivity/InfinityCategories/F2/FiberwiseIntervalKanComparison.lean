module

public import SerrePositivity.InfinityCategories.F2.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.F2.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.F2.ContinuousKanWeakEquivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
概要：定値底の path 全空間の Kan 模型から、元の全空間の Kan 模型の path 空間への比較。
方針：両端評価を固定し、anodyne な単位を Kan な両端評価に対して持ち上げる。
規約：両端は元の二つの評価の Kan 置換そのもの。
使われ方：一般 coherent な cospan の指定 path を保つ引き戻し比較。
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

/-- 概要：Kan 複体の path の両端評価は Kan fibration。
方針：単射な二点の境界への制限と標準評価同型を使う。
規約：始点・終点の順。使われ方：比較射の両端を固定した持ち上げ。 -/
instance arrowEndpointPair_fibration (X : SSet.{u}) [KanComplex X] :
    Fibration (arrowEndpointPair X) := by
  rw [arrowEndpointPair_restriction]
  infer_instance

/-- 概要：元の path を単位で写した両端は、元の評価の Kan 置換の単位と一致する。
方針：端点評価と Kan 置換の単位の自然性を合成する。
規約：元の評価射を保持。使われ方：両端固定の比較の可換四角形。 -/
lemma fiberwiseIntervalEndpoint_unit {E B : SSet.{u}} (p : E ⟶ B) (e : Fin 2) :
    (pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) ≫
      (ihom (Δ[1] : SSet.{u})).map (continuousKanReplacementUnit.app E)) ≫
        (intervalEndpointNatTrans e).app (continuousKanReplacement.obj E) =
      continuousKanReplacementUnit.app (fiberwiseFunctorSpace p Δ[1]) ≫
        continuousKanReplacement.map (fiberwiseIntervalEndpoint p e) := by
  have hn : (ihom (Δ[1] : SSet.{u})).map (continuousKanReplacementUnit.app E) ≫
      (intervalEndpointNatTrans e).app (continuousKanReplacement.obj E) =
      (intervalEndpointNatTrans e).app E ≫ continuousKanReplacementUnit.app E :=
    (intervalEndpointNatTrans e).naturality (continuousKanReplacementUnit.app E)
  rw [Category.assoc, hn, ← Category.assoc]
  exact continuousKanReplacementUnit.naturality (fiberwiseIntervalEndpoint p e)

/-- 概要：元の path と指定した両端の Kan 模型の可換四角形。
方針：二つの端点の単位式を組にする。
規約：両端の元の評価の Kan 置換。使われ方：指定両端の比較射の選択。 -/
lemma fiberwiseIntervalKanComparisonSquare {E B : SSet.{u}} (p : E ⟶ B) :
    CommSq
      (pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) ≫
        (ihom (Δ[1] : SSet.{u})).map (continuousKanReplacementUnit.app E))
      (continuousKanReplacementUnit.app (fiberwiseFunctorSpace p Δ[1]))
      (arrowEndpointPair (continuousKanReplacement.obj E))
      (lift (continuousKanReplacement.map (fiberwiseIntervalEndpoint p 0))
        (continuousKanReplacement.map (fiberwiseIntervalEndpoint p 1))) := ⟨by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [arrowEndpointPair, intervalEndpointNatTrans, Category.assoc, lift_fst] using
      fiberwiseIntervalEndpoint_unit p 0
  · simpa only [arrowEndpointPair, intervalEndpointNatTrans, Category.assoc, lift_snd] using
      fiberwiseIntervalEndpoint_unit p 1⟩

/-- 概要：定値底の全 path の Kan 模型から元の全空間 Kan 模型の path への比較。
方針：単位の anodyne 性と Kan な両端評価で指定四角形を持ち上げる。
規約：両端を同時に保持する選択。使われ方：一般 coherent な引き戻し比較。 -/
def fiberwiseIntervalKanComparison {E B : SSet.{u}} (p : E ⟶ B) :
    continuousKanReplacement.obj (fiberwiseFunctorSpace p Δ[1]) ⟶
      (ihom (Δ[1] : SSet.{u})).obj (continuousKanReplacement.obj E) := by
  have := continuousKanReplacementUnit_anodyne (fiberwiseFunctorSpace p Δ[1])
    (arrowEndpointPair (continuousKanReplacement.obj E))
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  exact (fiberwiseIntervalKanComparisonSquare p).lift

end SerrePositivity.InfinityCategories.F2
