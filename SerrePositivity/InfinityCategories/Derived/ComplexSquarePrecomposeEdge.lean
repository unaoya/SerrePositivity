module
public import SerrePositivity.InfinityCategories.Derived.ComplexSquarePrecomposeJoin
public import SerrePositivity.InfinityCategories.Derived.CofiberFiberComparisonProjection
public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagram

/-! # 四角形の前合成の slice 辺

概要：cospan を固定した前合成比較を実際の slice 辺と四角形全体の辺へ移す。
方針：join を curry し、始点射影を比較三単体の最初の辺で計算する。
規約：極限性は仮定しない。使われ方：D7 の suspension の比較射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.ComplexSquareData
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S] {V A B C D : Complex S}
variable (s : ComplexSquareData A B C D) (p : V ⟶ A)

/-- 前合成比較の join 写像は元の cospan を固定する。 -/
lemma precomposeJoin_fixed :
    joinInr (Δ[1] : SSet.{u + 1}) (SSet.horn 2 2) ≫ s.precomposeJoin p =
      pullbackCospan s.square := by
  calc
    _ = (joinInr (Δ[0] : SSet.{u + 1}) (SSet.horn 2 2) ≫
        joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet.{u + 1}))) ≫
        s.precomposeJoin p := by rw [joinInr_joinMap, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, precomposeJoin_face_zero]
      exact (pullbackCone s.square).property

/-- 前合成した四角形を元の cospan の上の錐として読む。 -/
def precomposeCone : JoinCone (pullbackCospan s.square) :=
  ⟨(pullbackCone (s.precompose p).square).val, by
    rw [← precomposeJoin_face_one, ← Category.assoc, joinInr_joinMap, Category.id_comp]
    exact s.precomposeJoin_fixed p⟩

/-- 四角形の前合成を表す実際の slice 辺。 -/
def precomposeSliceEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (sliceOver (pullbackCospan s.square)))
      (s.precomposeCone p) (pullbackCone s.square) where
  edge := SSet.yonedaEquiv (sliceOverCurry (s.precomposeJoin p) (s.precomposeJoin_fixed p))
  src_eq := sliceOverCurry_vertex_of_join _ _ 1 _ (s.precomposeJoin_face_one p)
  tgt_eq := sliceOverCurry_vertex_of_join _ _ 0 _ (s.precomposeJoin_face_zero p)

/-- Join の左因子は前合成射 p。 -/
lemma precomposeJoin_prefix :
    joinInl (Δ[1] : SSet.{u + 1}) (SSet.horn 2 2) ≫ s.precomposeJoin p =
      SSet.yonedaEquiv.symm (complexEdge p).edge := by
  rw [← cospanJoinLeft_firstEdge, Category.assoc, precomposeJoin_left,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  exact prepend_triangle_firstEdge _ _

/-- Slice の前合成比較辺の始点射影は p の辺。 -/
lemma precomposeSliceEdge_projection :
    ((s.precomposeSliceEdge p).map ((SSet.truncation 2).map
      (sliceOverProjection (pullbackCospan s.square)))).edge = (complexEdge p).edge := by
  change (sliceOverProjection (pullbackCospan s.square)).app _
    (SSet.yonedaEquiv (sliceOverCurry (s.precomposeJoin p) (s.precomposeJoin_fixed p))) = _
  rw [← SSet.yonedaEquiv_comp, sliceOverCurry_projection, precomposeJoin_prefix]
  exact SSet.yonedaEquiv.apply_symm_apply _

/-- Slice 比較を四角形全体の関手単体集合の辺へ写す。 -/
def precomposeSquareEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj
      ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (dgNerve S (Complex S))))
      (functorVertex (s.precompose p).square) (functorVertex s.square) := by
  let e := (s.precomposeSliceEdge p).map ((SSet.truncation 2).map
    (sliceSquareDiagramMap (pullbackCospan s.square)))
  refine ⟨e.edge, e.src_eq.trans ?_, e.tgt_eq.trans ?_⟩
  · change (sliceSquareDiagramMap (pullbackCospan s.square)).app (Opposite.op ⦋0⦌)
      (s.precomposeCone p) = _
    rw [sliceSquareDiagramMap_vertex]
    change functorVertex (cospanConeSquareIso.inv ≫
      (cospanConeSquareIso.hom ≫ (s.precompose p).square)) = _
    rw [Iso.inv_hom_id_assoc]
  · exact sliceSquareDiagramMap_pullbackCone s.square

end SerrePositivity.InfinityCategories.ComplexSquareData
