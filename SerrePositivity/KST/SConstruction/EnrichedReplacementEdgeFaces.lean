module
public import SerrePositivity.KST.SConstruction.PinchedComparisonDecoding
public import SerrePositivity.KST.SConstruction.CoherentSavedConstantEdges
public import SerrePositivity.KST.SConstruction.CoherentTetrahedronWhiskeredEdges

/-! # 元の比較四面体の四辺を元の比較辺と恒等辺へ照合
概要：保存した比較四面体の二経路の下辺を元の辺・復号辺へ、両上辺を恒等辺へ照合する。
方針：指定 pinched 面の全復号、標準面の定数性、元の四面体の豊穣合成を合わせる。
規約：元の全三面を持つ同じ四面体を入力とし、新しい辺・三角形を選ばない。
使われ方：元の BF 比較辺と合成面の復号辺を実二次元比較で接続する。
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

/-- 第一経路の下辺は、元の指定 pinched 比較面を作った同じ豊穣辺全体。 -/
lemma enrichedReplacementFirstLower_heq :
    HEq ((SimplicialCategory.sHom (T.simplex.obj (.mk (ULift.up 0)))
      (T.simplex.obj (.mk (ULift.up 3)))).δ 2
        (coherentSimplexFirstInsertionTriangle T.simplex 0 1 2 3
          (by decide) (by decide) (by decide)).simplex) e.edge := by
  have hl := coherentSimplexFirstInsertion_lower T.simplex 0 1 2 3
    (by decide) (by decide) (by decide)
  have hn := coherentSimplexCompositionEdge_naturality T.simplex
    (SimplexCategory.δ (2 : Fin 4)) 0 1 2 (by decide) (by decide)
  exact (heq_of_eq hl).trans ((heq_of_eq hn.symm).trans
    ((coherentSimplexCompositionEdge_heq T.replacement_face 0 1 2
      (by decide) (by decide)).trans (enrichedComparisonPinchedTriangle_decoded_heq e)))

/-- 第二経路の下辺は、同じ四面体から得た元の合成面の全復号辺。 -/
lemma enrichedReplacementSecondLower_heq :
    HEq ((SimplicialCategory.sHom (T.simplex.obj (.mk (ULift.up 0)))
      (T.simplex.obj (.mk (ULift.up 3)))).δ 2
        (coherentSimplexSecondInsertionTriangle T.simplex 0 1 2 3
          (by decide) (by decide) (by decide)).simplex)
      (coherentTriangleMappingEdge f g h T.triangle).edge :=
  (heq_of_eq (coherentSimplexSecondInsertion_lower T.simplex 0 1 2 3
    (by decide) (by decide) (by decide))).trans
    (coherentTetrahedronFaceComparison_heq T.simplex 1 f g h T.triangle T.triangle_face.symm)

/-- 第一経路の上辺全体は、元の合成射の頂点における同じ恒等辺。 -/
lemma enrichedReplacementFirstUpper_heq :
    HEq ((SimplicialCategory.sHom (T.simplex.obj (.mk (ULift.up 0)))
      (T.simplex.obj (.mk (ULift.up 3)))).δ 0
        (coherentSimplexFirstInsertionTriangle T.simplex 0 1 2 3
          (by decide) (by decide) (by decide)).simplex)
      (SSet.Edge.id (SimplicialCategory.homEquiv' X Z (f ≫ g))).edge := by
  have hu := coherentTetrahedronFirstUpper_heq T.simplex (𝟙 X) f g f (f ≫ g)
    (coherentNerveUnitCompStruct f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g)
    (T.unit_face.trans (coherentNerveUnitCompStruct_simplex f).symm) T.original_face
  have hc : (SimplicialCategory.sHomComp X X Z).app (Opposite.op ⦋1⦌)
      ((SSet.Edge.id (SimplicialCategory.homEquiv' X X (𝟙 X))).edge,
        (coherentTriangleMappingEdge f g (f ≫ g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g)).edge) =
      (SSet.Edge.id (SimplicialCategory.homEquiv' X Z (f ≫ g))).edge := by
    rw [coherentNerveCompStruct_decoded_edge]
    exact (simplicialHom_identityEdges_comp (𝟙 X) (f ≫ g)).trans
      (congrArg (fun k : X ⟶ Z => (SSet.Edge.id (SimplicialCategory.homEquiv' X Z k)).edge)
        (Category.id_comp (f ≫ g)))
  exact hu.trans (heq_of_eq hc)

/-- 第二経路の上辺全体も、元の同じ合成射の頂点における同じ恒等辺。 -/
lemma enrichedReplacementSecondUpper_heq :
    HEq ((SimplicialCategory.sHom (T.simplex.obj (.mk (ULift.up 0)))
      (T.simplex.obj (.mk (ULift.up 3)))).δ 0
        (coherentSimplexSecondInsertionTriangle T.simplex 0 1 2 3
          (by decide) (by decide) (by decide)).simplex)
      (SSet.Edge.id (SimplicialCategory.homEquiv' X Z (f ≫ g))).edge := by
  have hu := coherentTetrahedronSecondUpper_heq T.simplex (𝟙 X) f g f (f ≫ g)
    (coherentNerveUnitCompStruct f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g)
    (T.unit_face.trans (coherentNerveUnitCompStruct_simplex f).symm) T.original_face
  have hc : (SimplicialCategory.sHomComp X Y Z).app (Opposite.op ⦋1⦌)
      ((coherentTriangleMappingEdge (𝟙 X) f f (coherentNerveUnitCompStruct f)).edge,
        (SSet.Edge.id (SimplicialCategory.homEquiv' Y Z g)).edge) =
      (SSet.Edge.id (SimplicialCategory.homEquiv' X Z (f ≫ g))).edge := by
    rw [coherentNerveUnitCompStruct_decoded_edge]
    exact simplicialHom_identityEdges_comp f g
  exact hu.trans (heq_of_eq hc)

end SerrePositivity.KST.SConstruction
