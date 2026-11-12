module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofPointSliceEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofSliceOneSimplexOfTriangle

/-! # 実合成三角形の実 slice 辺

概要：指定実合成三角形を、指定両端・指定始域成分を持つ実 slice 辺へ戻す。
方針：三角形の全体を保存する実 slice 一単体を取り、三面を照合する。
規約：三角形もその辺も選び直さない。使われ方：反転関手の屋根評価を全空間内で比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

private lemma triangleFace₁ {X : SSet.{u}} {x y z : X _⦋0⦌}
    {a : Truncated.Edge (X := (truncation 2).obj X) x y}
    {b : Truncated.Edge (X := (truncation 2).obj X) y z}
    {c : Truncated.Edge (X := (truncation 2).obj X) x z}
    (T : Truncated.Edge.CompStruct a b c) :
    SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm T.simplex) = c.edge := by
  rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
  exact T.d₁

private lemma triangleFace₀ {X : SSet.{u}} {x y z : X _⦋0⦌}
    {a : Truncated.Edge (X := (truncation 2).obj X) x y}
    {b : Truncated.Edge (X := (truncation 2).obj X) y z}
    {c : Truncated.Edge (X := (truncation 2).obj X) x z}
    (T : Truncated.Edge.CompStruct a b c) :
    SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm T.simplex) = b.edge := by
  rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
  exact T.d₀

private lemma triangleFace₂ {X : SSet.{u}} {x y z : X _⦋0⦌}
    {a : Truncated.Edge (X := (truncation 2).obj X) x y}
    {b : Truncated.Edge (X := (truncation 2).obj X) y z}
    {c : Truncated.Edge (X := (truncation 2).obj X) x z}
    (T : Truncated.Edge.CompStruct a b c) :
    SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm T.simplex) = a.edge := by
  rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
  exact T.d₂

/-- 指定実合成三角形から、同じ三角形を記憶する実 slice 一単体を作る。 -/
def roofPointSliceCompositionSimplex {X : SSet.{u}} {x y z : X _⦋0⦌}
    {a : Truncated.Edge (X := (truncation 2).obj X) x y}
    {b : Truncated.Edge (X := (truncation 2).obj X) y z}
    {c : Truncated.Edge (X := (truncation 2).obj X) x z}
    (T : Truncated.Edge.CompStruct a b c) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) _⦋1⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceOneSimplexOfTriangle _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex b)
    (SSet.yonedaEquiv.symm T.simplex) (by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_edge b]
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
      exact T.d₀.trans (SSet.yonedaEquiv.apply_symm_apply b.edge).symm)

/-- 作った slice 一単体は、元の実三角形全体を厳密に回収する。 -/
lemma roofPointSliceCompositionSimplex_triangle {X : SSet.{u}} {x y z : X _⦋0⦌}
    {a : Truncated.Edge (X := (truncation 2).obj X) x y}
    {b : Truncated.Edge (X := (truncation 2).obj X) y z}
    {c : Truncated.Edge (X := (truncation 2).obj X) x z}
    (T : Truncated.Edge.CompStruct a b c) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle (SSet.yonedaEquiv.symm z) (roofPointSliceCompositionSimplex T) =
      SSet.yonedaEquiv.symm T.simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceOneSimplexOfTriangle_triangle _ _ _ _

/-- 指定実三角形を、長辺の slice 頂点から後半辺の slice 頂点への実辺へ戻す。 -/
def roofPointSliceCompositionEdge {X : SSet.{u}} {x y z : X _⦋0⦌}
    {a : Truncated.Edge (X := (truncation 2).obj X) x y}
    {b : Truncated.Edge (X := (truncation 2).obj X) y z}
    {c : Truncated.Edge (X := (truncation 2).obj X) x z}
    (T : Truncated.Edge.CompStruct a b c) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)).Edge
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex c) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex b) where
  edge := roofPointSliceCompositionSimplex T
  src_eq := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)).δ 1
      (roofPointSliceCompositionSimplex T) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex c
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg _ (roofPointSliceCompositionSimplex T) (1 : Fin 2)
    rw [roofPointSliceCompositionSimplex_triangle] at h
    exact h.symm.trans ((triangleFace₁ T).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_edge c).symm)
  tgt_eq := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)).δ 0
      (roofPointSliceCompositionSimplex T) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex b
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg _ (roofPointSliceCompositionSimplex T) (0 : Fin 2)
    rw [roofPointSliceCompositionSimplex_triangle] at h
    exact h.symm.trans ((triangleFace₀ T).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_edge b).symm)

/-- 実三角形の slice 辺の始域成分は、元の最初の辺そのもの。 -/
lemma roofPointSliceCompositionEdge_projection {X : SSet.{u}} {x y z : X _⦋0⦌}
    {a : Truncated.Edge (X := (truncation 2).obj X) x y}
    {b : Truncated.Edge (X := (truncation 2).obj X) y z}
    {c : Truncated.Edge (X := (truncation 2).obj X) x z}
    (T : Truncated.Edge.CompStruct a b c) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)).app (Opposite.op ⦋1⦌)
      (roofPointSliceCompositionEdge T).edge = a.edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)).app (Opposite.op ⦋1⦌)
    (roofPointSliceCompositionSimplex T) = _
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_base _ (roofPointSliceCompositionSimplex T)
  rw [roofPointSliceCompositionSimplex_triangle] at h
  exact h.symm.trans (triangleFace₂ T)

/-- 恒等 slice 頂点から回収する辺は、元の恒等辺。 -/
lemma roofPointSliceIdentityCone_edge {X : SSet.{u}} (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone x)).edge =
      (Truncated.Edge.id (X := (truncation 2).obj X) x).edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ SSet.const x) = _
  rw [SSet.comp_const]
  change X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op x =
    X.map (SimplexCategory.σ (0 : Fin 1)).op x
  exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ => X.map α.op x) (Subsingleton.elim _ _)

/-- 恒等辺から作った slice 頂点は、標準恒等 slice 頂点そのもの。 -/
lemma roofPointSliceEdgeVertex_id {X : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex (Truncated.Edge.id (X := (truncation 2).obj X) x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone x := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_edge, roofPointSliceIdentityCone_edge]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
