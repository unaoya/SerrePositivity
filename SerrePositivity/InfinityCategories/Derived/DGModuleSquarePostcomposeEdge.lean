module
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquarePostcomposeJoin
public import SerrePositivity.InfinityCategories.Derived.FiberCofiberComparisonProjection
public import SerrePositivity.InfinityCategories.Derived.DGModuleTriangleAppendEdge
public import SerrePositivity.InfinityCategories.Stable.CosliceSquareDiagram

/-! # 四角形の後合成の coslice 辺

概要：span を固定した後合成比較を coslice の実際の辺へ移す。
方針：join を curry し、終点射影を比較三単体の最後の辺で計算する。
規約：余極限性は仮定しない。使われ方：D7 の suspension の比較射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGModuleSquareData
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable {W X Y Z T : ModuleCategory A D}
variable (s : DGModuleSquareData A D W X Y Z) (q : Z ⟶ T)

/-- 後合成比較の join 写像は元の span を固定する。 -/
lemma postcomposeJoin_fixed :
    joinInl (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[1] ≫ s.postcomposeJoin q =
      pushoutSpan s.square := by
  calc
    _ = (joinInl (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[0] ≫
        joinMap (𝟙 (SSet.horn 2 0 : SSet.{max (u + 1) v})) (SSet.stdSimplex.δ (1 : Fin 2))) ≫
        s.postcomposeJoin q := by rw [joinInl_joinMap, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, postcomposeJoin_face_one]
      exact (pushoutCocone s.square).property

/-- 後合成した四角形を元の span の上の余錐として読む。 -/
def postcomposeCocone : JoinCocone (pushoutSpan s.square) :=
  ⟨(pushoutCocone (s.postcompose q).square).val, by
    rw [← postcomposeJoin_face_zero, ← Category.assoc, joinInl_joinMap, Category.id_comp]
    exact s.postcomposeJoin_fixed q⟩

/-- 四角形の後合成を表す実際の coslice 辺。 -/
def postcomposeSliceEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (sliceUnder (pushoutSpan s.square)))
      (pushoutCocone s.square) (s.postcomposeCocone q) where
  edge := SSet.yonedaEquiv (sliceUnderCurry (s.postcomposeJoin q) (s.postcomposeJoin_fixed q))
  src_eq := sliceUnderCurry_vertex_of_join _ _ 1 _ (s.postcomposeJoin_face_one q)
  tgt_eq := sliceUnderCurry_vertex_of_join _ _ 0 _ (s.postcomposeJoin_face_zero q)

/-- Join の右因子は後合成射 q。 -/
lemma postcomposeJoin_suffix :
    joinInr (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[1] ≫ s.postcomposeJoin q =
      SSet.yonedaEquiv.symm (dgModuleEdge A D q).edge := by
  rw [← spanJoinLeft_lastEdge, Category.assoc, postcomposeJoin_left,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  exact dgModuleTriangleAppend_lastEdge A D _ _ _ _ _ _

/-- Coslice の後合成比較辺の終点射影は q の辺。 -/
lemma postcomposeSliceEdge_projection :
    ((s.postcomposeSliceEdge q).map ((SSet.truncation 2).map
      (sliceUnderProjection (pushoutSpan s.square)))).edge = (dgModuleEdge A D q).edge := by
  change (sliceUnderProjection (pushoutSpan s.square)).app _
    (SSet.yonedaEquiv (sliceUnderCurry (s.postcomposeJoin q) (s.postcomposeJoin_fixed q))) = _
  rw [← SSet.yonedaEquiv_comp, sliceUnderCurry_projection, postcomposeJoin_suffix]
  exact SSet.yonedaEquiv.apply_symm_apply _

/-- Coslice 比較を四角形全体の関手単体集合の辺へ写す。 -/
def postcomposeSquareEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj
      ((ihom
        ((Δ[1] : SSet.{max (u + 1) v}) ⊗ Δ[1])).obj (dgModuleNerve A D)))
      (functorVertex s.square) (functorVertex (s.postcompose q).square) := by
  let e := (s.postcomposeSliceEdge q).map ((SSet.truncation 2).map
    (cosliceSquareDiagramMap (pushoutSpan s.square)))
  refine ⟨e.edge, e.src_eq.trans ?_, e.tgt_eq.trans ?_⟩
  · exact cosliceSquareDiagramMap_pushoutCocone s.square
  · change (cosliceSquareDiagramMap (pushoutSpan s.square)).app (Opposite.op ⦋0⦌)
      (s.postcomposeCocone q) = _
    rw [cosliceSquareDiagramMap_vertex]
    change functorVertex (spanCoconeSquareIso.inv ≫
      (spanCoconeSquareIso.hom ≫ (s.postcompose q).square)) = _
    rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.DGModuleSquareData
