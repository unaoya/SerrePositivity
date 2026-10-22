module
public import SerrePositivity.KST.SConstruction.PointedSpanEnrichment

/-! # 元の span の各頂点への標準 end 評価関手
概要：元の三頂点の評価を、全 Hom と同じ恒等・合成を保つ豊穣関手にする。
方針：標準 end の単位と合成の射影式を使う。
規約：元の図式の値を変更しない。使われ方：実押し出しの単位・合成の検出。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 元の span の一頂点への全 Hom 評価は、厳密単体的豊穣関手。 -/
def pointedSpanEvaluationFunctor (i : WalkingSpan) :
    EnrichedFunctor SSet.{u} PointedSpanDiagram.{u} PointedSSetObject.{u} where
  obj X := X.diagram.obj i
  map X Y := pointedSpanProjection X Y i
  map_id X := Enriched.FunctorCategory.enrichedId_π SSet X.diagram i
  map_comp X Y Z := Enriched.FunctorCategory.enrichedComp_π SSet X.diagram Y.diagram Z.diagram i

/-- 元の通常の自然変換の全 Hom 評価は、同じ通常成分を回収する。 -/
lemma pointedSpanProjection_hom {X Y : PointedSpanDiagram.{u}} (t : X ⟶ Y) (i : WalkingSpan) :
    eHomEquiv SSet t ≫ pointedSpanProjection X Y i = eHomEquiv SSet (t.app i) :=
  Enriched.FunctorCategory.homEquiv_apply_π SSet t i

end SerrePositivity.KST.SConstruction
