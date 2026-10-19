module
public import SerrePositivity.InfinityCategories.Derived.DGTriangleSourceRefinement

/-! # 始点細分した実三角形の三面と全成分

概要：実細分三角形は元の辺 12 を保ち、二辺と三角 cochain は指定閉射の前合成と一致する。
方針：三角形データの両逆性と既存の三面公式を使う。
規約：全て実単体と元の Hom の等式。使われ方：三面を共通辺に沿って貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable (t : Simplex A D 2) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))

/-- 実始点細分の辺 01 は、元の辺の指定閉射による前合成。 -/
lemma dgSimplexSourceRefinement_edge01 :
    (dgSimplexSourceRefinement t q s).edgeHom 0 1 (by decide) =
      dgGradedPrecompose A D 0 (t.edgeHom 0 1 (by decide)) s := rfl

/-- 実始点細分の辺 02 も同じ指定閉射による前合成。 -/
lemma dgSimplexSourceRefinement_edge02 :
    (dgSimplexSourceRefinement t q s).edgeHom 0 2 (by decide) =
      dgGradedPrecompose A D 0 (t.edgeHom 0 2 (by decide)) s := rfl

/-- 実始点細分の辺 12 の cochain は元のまま。 -/
lemma dgSimplexSourceRefinement_edge12 :
    (dgSimplexSourceRefinement t q s).edgeHom 1 2 (by decide) = t.edgeHom 1 2 (by decide) := rfl

/-- 実始点細分の三角 cochain は、元の三角 cochain の同じ指定閉射による前合成。 -/
lemma dgSimplexSourceRefinement_triangle :
    (dgSimplexSourceRefinement t q s).triangleHom =
      dgGradedPrecompose A D (-1) t.triangleHom s := rfl

/-- 実始点細分の零面は、元の指定辺 12 の一次単体そのもの。 -/
lemma dgSimplexSourceRefinement_face0 :
    (dgNerve A D).δ 0 (dgSimplexSourceRefinement t q s) = (dgNerve A D).δ 0 t := by
  have h := congrArg ((dgNerve A D).δ (0 : Fin 3)) (Simplex.ofTriangle_toTriangle t)
  rw [triangle_face12] at h
  exact (triangle_face12 (dgTriangleSourceRefinement t.toTriangle q s)).trans h

/-- 実始点細分の二面は、指定閉射による辺 01 の前合成を持つ実辺。 -/
lemma dgSimplexSourceRefinement_face2 :
    (dgNerve A D).δ 2 (dgSimplexSourceRefinement t q s) =
      Simplex.ofEdge (pairObj q (t.obj 1))
        (dgClosedCyclePrecompose (t.edgeCycle 0 1 (by decide)) s) :=
  triangle_face01 (dgTriangleSourceRefinement t.toTriangle q s)

/-- 実始点細分の一面は、同じ閉射による辺 02 の前合成を持つ実辺。 -/
lemma dgSimplexSourceRefinement_face1 :
    (dgNerve A D).δ 1 (dgSimplexSourceRefinement t q s) =
      Simplex.ofEdge (pairObj q (t.obj 2))
        (dgClosedCyclePrecompose (t.edgeCycle 0 2 (by decide)) s) :=
  triangle_face02 (dgTriangleSourceRefinement t.toTriangle q s)

end SerrePositivity.InfinityCategories
