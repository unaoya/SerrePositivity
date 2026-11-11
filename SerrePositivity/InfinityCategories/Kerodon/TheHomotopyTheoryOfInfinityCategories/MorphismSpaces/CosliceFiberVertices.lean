module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.VertexFiberPullback
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice

/-!
概要：coslice 射影の fiber の頂点と、二端点を指定した辺の対応。
方針：Δ[0] ⋆ Δ[0] ≅ Δ[1] と Yoneda の同値で互いに逆な写像を作る。
規約：quasicategory 性を仮定しない。左端を始点、右端を終点とする。
使われ方：Kerodon §4.6.5（Tag 01KW）、Construction 5.5.2.1（Tag 01ZW）、pointed-space fiber の零次比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：二点の join の左包含は一単体の始点の面。
方針：標準単体の join の左包含の計算を零次元で特殊化する。
規約：δ 1 が始点。
使われ方：Kerodon §4.6.5（Tag 01KW）、coslice の固定端点の計算。 -/
lemma joinPoints_inl_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom =
      stdSimplex.δ 1 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inl]
  congr 1
  ext i
  fin_cases i
  rfl

/-- 概要：二点の join の右包含は一単体の終点の面。
方針：標準単体の join の右包含の計算を零次元で特殊化する。
規約：δ 0 が終点。
使われ方：Kerodon §4.6.5（Tag 01KW）、coslice 射影の零次成分の計算。 -/
lemma joinPoints_inr_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom =
      stdSimplex.δ 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inr]
  congr 1
  ext i
  fin_cases i
  rfl

/-- 概要：始点の面を join に戻すと左包含になる。
方針：join の同型の順方向を右から消去する。
規約：二因子とも標準零単体。
使われ方：Kerodon §4.6.5（Tag 01KW）、fiber の頂点から辺への構成。 -/
lemma joinPoints_face_inl :
    stdSimplex.δ 1 ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] Δ[0] := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, joinPoints_inl_face]

/-- 概要：終点の面を join に戻すと右包含になる。
方針：join の同型の順方向を右から消去する。
規約：二因子とも標準零単体。
使われ方：Kerodon §4.6.5（Tag 01KW）、fiber の頂点の終点の確認。 -/
lemma joinPoints_face_inr :
    stdSimplex.δ 0 ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[0] := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, joinPoints_inr_face]

/-- 概要：coslice 射影の y 上の fiber の頂点から x→y の辺を取り出す。
方針：join を一単体に直し、二つの制限条件を面の等式に変換する。
規約：固定図式は x に対応する Δ[0] からの射。
使われ方：Kerodon §4.6.5（Tag 01KW）、pointed space の頂点を点からの辺として読む。 -/
def cosliceFiberVertexToEdge {X : SSet.{u}} {x y : X _⦋0⦌}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋0⦌) :
    X.Edge x y :=
  SSet.Edge.mk (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ s.val.val))
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, joinPoints_face_inl,
        s.val.property, Equiv.apply_symm_apply])
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, joinPoints_face_inr]
      exact s.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero y))

/-- 概要：二端点を指定した辺から coslice 射影の fiber の頂点を作る。
方針：一単体を二点の join に移し、辺の面の条件を使う。
規約：底の頂点は終点 y。
使われ方：Kerodon Construction 5.5.2.1（Tag 01ZW）、空間の点から pointed space の頂点を作る。 -/
def edgeToCosliceFiberVertex {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋0⦌ := by
  refine ⟨⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge, ?_⟩, ?_⟩
  · rw [← Category.assoc, joinPoints_inl_face, e.δ_one_yonedaEquiv_symm]
  · change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[0] ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge)) = _
    rw [← Category.assoc, joinPoints_inr_face, e.δ_zero_yonedaEquiv_symm,
      Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]

/-- 概要：coslice の fiber の頂点は始点と終点を指定した辺と同値。
方針：join の同型と Yoneda の同値の逆写像則で両合成を計算する。
規約：これは零単体の型の同値であり、写像空間全体の同値とは区別する。
使われ方：Kerodon §4.6.5（Tag 01KW）、pointed-space fiber と Kan 複体の比較の零次部分。 -/
def cosliceFiberVertexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋0⦌ ≃
      X.Edge x y where
  toFun := cosliceFiberVertexToEdge
  invFun := edgeToCosliceFiberVertex
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ s.val.val)) = s.val.val
    rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  right_inv e := by
    apply SSet.Edge.ext
    change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge)) = e.edge
    rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
