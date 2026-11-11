module
public import SerrePositivity.KST.SConstruction.KPrismEndpointComposites
public import SerrePositivity.KST.SConstruction.CoherentTriangleMappingRawEdge
public import SerrePositivity.KST.SConstruction.CoherentThreeVertexRefinementEdges

/-! # 元の K の二円柱の指定成分は既存の二三角形の復号辺
概要：元の収縮の指定頂点での二脚を、元の square の既存の二三角形の実復号辺へ同定する。
方針：対象の等式による移送を消去し、同じ元の三角形と同じ Path 包含辺で比較する。
規約：元の実辺を保持し、Kan の充填や逆辺を選び直さない。
使われ方：既存 BF 境界の指定外側三角形を全精密化パラメータへ延長する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kPrismBoundaryLegs_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の写像空間の表示の同型は、全次数の同じ元の値と依存等号で一致する。 -/
lemma kKanOriginalPrismNativeHomIso_value_heq {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (x y : I) {d : ℕ}
    (v : (SimplicialCategory.sHom
      (coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (x, ULift.up 0))
      (coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (y, ULift.up 1))) _⦋d⦌) :
    HEq ((kKanOriginalPrismNativeHomIso r F x y).hom.app (Opposite.op ⦋d⦌) v) v :=
  coherentEqToHom_value_heq
    (congrArg₂ (fun A B : PointedSimplicialSet.{u} => (PointedObject.basedHom A B).right)
      (kKanOriginalPrismStringVertex_bottom r F x) (kKanOriginalPrismStringVertex_top r F y)) v

/-- 下側の元の円柱の指定成分は、元の square の同じ三角形の既存の復号辺。 -/
lemma kKanOriginalPrismLowerCompositeContraction_boundary_leg {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (kKanOriginalPrismLowerCompositeContraction r F f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))).edge =
      (coherentSquareMappingBottomRight (kKanSuspensionMappingTriangles r F f)).edge := by
  have hc := kKanOriginalPrismLowerCompositeContraction_vertex_edge r F f
  let s := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f)
  let P := (nerve.edgeMk (coherentStringRefinementPathToFull (coherentArrowStringDirectTo s))).edge
  have ht := kKanOriginalPrismNativeHomIso_value_heq r F x y
    ((coherentStringNativeMap (kKanOriginalPrismStringDiagram r F) s).app (Opposite.op ⦋1⦌) P)
  have hv := coherentStringNativeMap_value_heq (kKanOriginalPrismStringDiagram r F) s P
  have hp := coherentStringRefinementPathToFull_triangle_heq s rfl
  have he := coherentTriangleEdgeValue_heq (kKanOriginalPrismLowerDirect_cell r F f)
    (nerve.edgeMk (coherentEndpointPathToComposite
      (show (ULift.up 0 : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide)
      (show (ULift.up 1 : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide))).edge
  have hs := coherentTriangleMappingEdge_raw_heq _ _ _
    (kKanSuspensionMappingTriangles r F f).bottomRight
  have hp' := congrArg ((((kKanOriginalPrismStringDiagram r F).app (Opposite.op ⦋2⦌)
    (ULift.up s.chain)).map (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋1⦌))
      (eq_of_heq hp)
  exact eq_of_heq (hc.heq.trans (ht.trans (hv.trans (hp'.heq.trans (he.trans hs.symm)))))

/-- 上側の元の円柱の指定成分は、元の square の同じ三角形の既存の復号辺。 -/
lemma kKanOriginalPrismUpperCompositeContraction_boundary_leg {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (kKanOriginalPrismUpperCompositeContraction r F f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))).edge =
      (coherentSquareMappingLeftTop (kKanSuspensionMappingTriangles r F f)).edge := by
  have hc := kKanOriginalPrismUpperCompositeContraction_vertex_edge r F f
  let s := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f)
  let P := (nerve.edgeMk (coherentStringRefinementPathToFull (coherentArrowStringDirectTo s))).edge
  have ht := kKanOriginalPrismNativeHomIso_value_heq r F x y
    ((coherentStringNativeMap (kKanOriginalPrismStringDiagram r F) s).app (Opposite.op ⦋1⦌) P)
  have hv := coherentStringNativeMap_value_heq (kKanOriginalPrismStringDiagram r F) s P
  have hp := coherentStringRefinementPathToFull_triangle_heq s rfl
  have he := coherentTriangleEdgeValue_heq (kKanOriginalPrismUpperDirect_cell r F f)
    (nerve.edgeMk (coherentEndpointPathToComposite
      (show (ULift.up 0 : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide)
      (show (ULift.up 1 : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide))).edge
  have hs := coherentTriangleMappingEdge_raw_heq _ _ _
    (kKanSuspensionMappingTriangles r F f).leftTop
  have hp' := congrArg ((((kKanOriginalPrismStringDiagram r F).app (Opposite.op ⦋2⦌)
    (ULift.up s.chain)).map (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋1⦌))
      (eq_of_heq hp)
  exact eq_of_heq (hc.heq.trans (ht.trans (hv.trans (hp'.heq.trans (he.trans hs.symm)))))

/-- 二円柱の元の共通初点は、同じ元の square の対角射の頂点そのもの。 -/
lemma kKanOriginalPrismSpanInitialVertex_diagonal {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    kKanOriginalPrismSpanInitialVertex r F f =
      PointedMapping.familyVertex (kKanSuspensionMappingTriangles r F f).diagonal := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (kKanOriginalPrismLowerCompositeContraction r F f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))
  have h := kKanOriginalPrismLowerCompositeContraction_boundary_leg r F f
  have hs := e.src_eq.symm.trans
    ((congrArg ((kKanOriginalSuspensionMappingTarget r F x y).map
      (SimplexCategory.δ (1 : Fin 2)).op) h).trans
        (coherentSquareMappingBottomRight (kKanSuspensionMappingTriangles r F f)).src_eq)
  have hv : kKanOriginalPrismSpanInitialVertex r F f =
      SimplicialCategory.homEquiv' _ _ (kKanSuspensionMappingTriangles r F f).diagonal := by
    simpa [e, SSet.const, SimplexCategory.const_eq_id] using hs
  exact hv.trans (PointedMapping.familyVertex_eq_pointedHomVertex _).symm

end SerrePositivity.KST.SConstruction
