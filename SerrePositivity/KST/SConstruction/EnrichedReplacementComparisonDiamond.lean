module
public import SerrePositivity.KST.SConstruction.EnrichedReplacementEdgeFaces
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondComposition

/-! # 保存した比較四面体から元の辺と復号辺を結ぶ実三角形対
概要：元の豊穣比較辺と保存した合成面の復号辺を、同じ対角辺へ結ぶ実三角形対にする。
方針：同じ Path 二単体を元の Hom へ表示移送し、上辺を同じ恒等辺として回収する。
規約：元の全二単体・指定比較面を保つ。追加の Kan 充填は使わない。
使われ方：元の BF 比較辺と保存した合成三角形の全復号辺の実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
  (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
  (e : (SimplicialCategory.sHom X Z).Edge (SimplicialCategory.homEquiv' _ _ h)
    (SimplicialCategory.homEquiv' _ _ (f ≫ g)))
  (T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionReplacementTetrahedron (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g)
    (enrichedComparisonPinchedTriangle e))
include f g h e T

/-- 保存した比較四面体の始終 Hom は元の二対象の同じ豊穣 Hom。 -/
lemma enrichedReplacementMappingSpace_eq :
    SimplicialCategory.sHom (T.simplex.obj (.mk (ULift.up 0)))
      (T.simplex.obj (.mk (ULift.up 3))) = SimplicialCategory.sHom X Z := by
  have hv := coherentTetrahedron_vertices T.simplex (𝟙 X) f g f (f ≫ g)
    (coherentNerveUnitCompStruct f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g)
    (T.unit_face.trans (coherentNerveUnitCompStruct_simplex f).symm) T.original_face
  exact congrArg₂ (fun A B : C => SimplicialCategory.sHom A B) hv.1 hv.2.2.2

/-- 比較四面体の二つの元の Path 三角形は、同じ実対角辺を共有する。 -/
lemma enrichedReplacementPathTriangles_diagonal :
    (SimplicialCategory.sHom (T.simplex.obj (.mk (ULift.up 0)))
      (T.simplex.obj (.mk (ULift.up 3)))).δ 1
        (coherentSimplexFirstInsertionTriangle T.simplex 0 1 2 3
          (by decide) (by decide) (by decide)).simplex =
      (SimplicialCategory.sHom (T.simplex.obj (.mk (ULift.up 0)))
        (T.simplex.obj (.mk (ULift.up 3)))).δ 1
          (coherentSimplexSecondInsertionTriangle T.simplex 0 1 2 3
            (by decide) (by decide) (by decide)).simplex :=
  coherentDoubleInsertMappedTriangles_diagonal
    (T.simplex.map (.mk (ULift.up (0 : Fin 4))) (.mk (ULift.up (3 : Fin 4))))
    (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 1 from by decide)
    (show (ULift.up (1 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide)
    (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 2 from by decide)
    (show (ULift.up (2 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide)
    (coherentEndpointPath (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide))

/-- 元の Hom 内の全二単体と全四辺・共通対角辺、および元の全単体の像の保存データ。 -/
def enrichedReplacementRawDiamondData :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondTransportData (enrichedReplacementMappingSpace_eq f g h e T)
    (coherentSimplexFirstInsertionTriangle T.simplex 0 1 2 3
      (by decide) (by decide) (by decide)).simplex
    (coherentSimplexSecondInsertionTriangle T.simplex 0 1 2 3
      (by decide) (by decide) (by decide)).simplex _ _ _ _
    (enrichedReplacementFirstLower_heq f g h e T)
    (enrichedReplacementSecondLower_heq f g h e T)
    (enrichedReplacementFirstUpper_heq f g h e T)
    (enrichedReplacementSecondUpper_heq f g h e T)
    (enrichedReplacementPathTriangles_diagonal f g h e T)

/-- 元の比較辺と全復号辺を同じ対角辺へ結ぶ実三角形対。元の全二単体も保存する。 -/
def enrichedReplacementComparisonData :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData e
    (SSet.Edge.id (SimplicialCategory.homEquiv' X Z (f ≫ g)))
    (coherentTriangleMappingEdge f g h T.triangle)
    (SSet.Edge.id (SimplicialCategory.homEquiv' X Z (f ≫ g)))
    (enrichedReplacementRawDiamondData f g h e T).val

/-- 元の比較辺と全復号辺を、同じ Hom 内の共通辺へ結ぶ同じ実三角形対。 -/
def enrichedReplacementComparison := (enrichedReplacementComparisonData f g h e T).val

/-- 第一の実比較三角形全体は、元の比較四面体の第一 Path 二単体の像そのもの。 -/
lemma enrichedReplacementComparison_first_image :
    (enrichedReplacementComparison f g h e T).first.simplex =
      (eqToHom (enrichedReplacementMappingSpace_eq f g h e T)).app (Opposite.op ⦋2⦌)
        (coherentSimplexFirstInsertionTriangle T.simplex 0 1 2 3
          (by decide) (by decide) (by decide)).simplex :=
  (enrichedReplacementComparisonData f g h e T).property.1.trans
    (enrichedReplacementRawDiamondData f g h e T).property.1

/-- 第二の実比較三角形全体も、元の同じ四面体の第二 Path 二単体の像そのもの。 -/
lemma enrichedReplacementComparison_second_image :
    (enrichedReplacementComparison f g h e T).second.simplex =
      (eqToHom (enrichedReplacementMappingSpace_eq f g h e T)).app (Opposite.op ⦋2⦌)
        (coherentSimplexSecondInsertionTriangle T.simplex 0 1 2 3
          (by decide) (by decide) (by decide)).simplex :=
  (enrichedReplacementComparisonData f g h e T).property.2.trans
    (enrichedReplacementRawDiamondData f g h e T).property.2

end SerrePositivity.KST.SConstruction
