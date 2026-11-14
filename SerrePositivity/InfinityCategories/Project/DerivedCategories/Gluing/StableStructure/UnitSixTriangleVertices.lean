module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.TriangleDiagramVertices
/-! # 共有六片の五頂点表示

概要：実六二単体の共有辺と三本の既知辺から、五頂点上の六片の頂点を全て回収する。
方針：共有辺の両端を比較し、係数三角形の中間頂点をそのまま使う。
規約：六二単体と既知の辺を保持し、単位閉路の消去は要求しない。
使われ方：六つの実合成構造を同じ型付き図式へ接続する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open scoped _root_.Simplicial

def dgGluingUnitSixTriangleVertexPattern {Z : SSet.{u}} (a b c d e : Z _⦋0⦌) :
    Fin 6 → Fin 3 → Z _⦋0⦌ := ![![a,b,b], ![a,c,b], ![d,d,e], ![d,c,e], ![d,c,b], ![a,c,e]]

lemma dgGluingUnitSixTriangle_vertices {Z : SSet.{u}} {a b d e : Z _⦋0⦌}
    (T : Fin 6 → ((Δ[2] : SSet.{u}) ⟶ Z))
    (df : Truncated.Edge (X := (truncation 2).obj Z) a b)
    (dl : Truncated.Edge (X := (truncation 2).obj Z) d e)
    (k : Truncated.Edge (X := (truncation 2).obj Z) d b)
    (hdf : SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ T 0) = df.edge)
    (hdl : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T 2) = dl.edge)
    (hk : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T 4) = k.edge)
    (h01 : stdSimplex.δ (1 : Fin 3) ≫ T 0 = stdSimplex.δ (1 : Fin 3) ≫ T 1)
    (h23 : stdSimplex.δ (1 : Fin 3) ≫ T 2 = stdSimplex.δ (1 : Fin 3) ≫ T 3)
    (h15 : stdSimplex.δ (2 : Fin 3) ≫ T 1 = stdSimplex.δ (2 : Fin 3) ≫ T 5)
    (h35 : stdSimplex.δ (0 : Fin 3) ≫ T 3 = stdSimplex.δ (0 : Fin 3) ≫ T 5)
    (h14 : stdSimplex.δ (0 : Fin 3) ≫ T 1 = stdSimplex.δ (0 : Fin 3) ≫ T 4)
    (h34 : stdSimplex.δ (2 : Fin 3) ≫ T 3 = stdSimplex.δ (2 : Fin 3) ≫ T 4) :
    ∀ i j, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T i) j =
      dgGluingUnitSixTriangleVertexPattern a b (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T 4) 1) d e i j := by
  have source {i j : Fin 6} {p q : Fin 3}
      (h : stdSimplex.δ p ≫ T i = stdSimplex.δ q ≫ T j) :
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T i) (![1,0,0] p) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T j) (![1,0,0] q) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleFace_source] using
      congrArg (fun f => Z.δ 1 (SSet.yonedaEquiv f)) h
  have target {i j : Fin 6} {p q : Fin 3}
      (h : stdSimplex.δ p ≫ T i = stdSimplex.δ q ≫ T j) :
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T i) (![2,2,1] p) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T j) (![2,2,1] q) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleFace_target] using
      congrArg (fun f => Z.δ 0 (SSet.yonedaEquiv f)) h
  have ha : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T 0) 0 = a := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleFace_source (T 0) 2).symm.trans
      ((congrArg (fun t => Z.δ 1 t) hdf).trans df.src_eq)
  have hb : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T 0) 1 = b := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleFace_target (T 0) 2).symm.trans
      ((congrArg (fun t => Z.δ 0 t) hdf).trans df.tgt_eq)
  have hd : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T 2) 1 = d := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleFace_source (T 2) 0).symm.trans
      ((congrArg (fun t => Z.δ 1 t) hdl).trans dl.src_eq)
  have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T 2) 2 = e := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleFace_target (T 2) 0).symm.trans
      ((congrArg (fun t => Z.δ 0 t) hdl).trans dl.tgt_eq)
  have hkd : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T 4) 0 = d := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleFace_source (T 4) 1).symm.trans
      ((congrArg (fun t => Z.δ 1 t) hk).trans k.src_eq)
  have hkb : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T 4) 2 = b := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleFace_target (T 4) 1).symm.trans
      ((congrArg (fun t => Z.δ 0 t) hk).trans k.tgt_eq)
  intro i j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · exact (target h01).trans ((target h14).trans hkb)
  · exact (source h01).symm.trans ha
  · exact source h14
  · exact (target h14).trans hkb
  · exact (source h23).trans ((source h34).trans hkd)
  · exact hd
  · exact he
  · exact (source h34).trans hkd
  · exact target h34
  · exact (target h23).symm.trans he
  · exact hkd
  · rfl
  · exact hkb
  · exact (source h15).symm.trans ((source h01).symm.trans ha)
  · exact (target h15).symm.trans (source h14)
  · exact (target h35).symm.trans ((target h23).symm.trans he)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
