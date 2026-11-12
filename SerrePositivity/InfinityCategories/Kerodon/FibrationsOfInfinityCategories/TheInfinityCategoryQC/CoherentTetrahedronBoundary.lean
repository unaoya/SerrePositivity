module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatTetrahedronLastFace

/-!
概要：coherent 三単体の六辺の四面間での一致。
方針：二通りの面の合成を単体恒等式で揃える。
規約：元の単体と指定射を厳密に保つ。
使われ方：coherent 三単体の指定関手同型の合成則。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
/-- 概要：等しい coherent 辺から読み戻した射は型を含めて等しい。
方針：辺の等式を消去する。
規約：両端点の型が変わることを許す。
使われ方：単体恒等式を読み戻した射の等式へ移す。 -/
lemma coherentEdgeHom_heq {s t : (SimplicialNerve C) _⦋1⦌} (h : s = t) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom s) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom t) := by cases h; rfl
/-- 概要：四面に現れる辺 13 の二つの表示は同じ射。
方針：単体恒等式と辺の読み戻しの関手性を使う。
規約：同型に弱めず射自体を同定する。
使われ方：四つの三角形の関手同型の両端を同時に揃える。 -/
lemma coherentTetrahedronBoundary13 (s : (SimplicialNerve C) _⦋3⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 0 ((SimplicialNerve C).δ 2 s)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 1 ((SimplicialNerve C).δ 0 s)) := by
  exact eq_of_heq (coherentEdgeHom_heq
    (ConcreteCategory.congr_hom
      ((SimplicialNerve C).δ_comp_δ (show (0 : Fin 3) ≤ 1 by decide)) s))
/-- 概要：四面に現れる辺 03 の二つの表示は同じ射。
方針：単体恒等式と辺の読み戻しの関手性を使う。
規約：同型に弱めず射自体を同定する。
使われ方：四つの三角形の関手同型の両端を同時に揃える。 -/
lemma coherentTetrahedronBoundary03 (s : (SimplicialNerve C) _⦋3⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 1 ((SimplicialNerve C).δ 1 s)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 1 ((SimplicialNerve C).δ 2 s)) := by
  exact eq_of_heq (coherentEdgeHom_heq
    (ConcreteCategory.congr_hom ((SimplicialNerve C).δ_comp_δ_self (i := (1 : Fin 3))) s))
/-- 概要：四面に現れる辺 02 の二つの表示は同じ射。
方針：単体恒等式と辺の読み戻しの関手性を使う。
規約：同型に弱めず射自体を同定する。
使われ方：四つの三角形の関手同型の両端を同時に揃える。 -/
lemma coherentTetrahedronBoundary02 (s : (SimplicialNerve C) _⦋3⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 2 ((SimplicialNerve C).δ 1 s)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 1 ((SimplicialNerve C).δ 3 s)) := by
  exact eq_of_heq (coherentEdgeHom_heq
    (ConcreteCategory.congr_hom
      ((SimplicialNerve C).δ_comp_δ (show (1 : Fin 3) ≤ 2 by decide)) s).symm)
/-- 概要：四面に現れる辺 23 の二つの表示は同じ射。
方針：単体恒等式と辺の読み戻しの関手性を使う。
規約：同型に弱めず射自体を同定する。
使われ方：四つの三角形の関手同型の両端を同時に揃える。 -/
lemma coherentTetrahedronBoundary23 (s : (SimplicialNerve C) _⦋3⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 0 ((SimplicialNerve C).δ 1 s)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 0 ((SimplicialNerve C).δ 0 s)) := by
  exact eq_of_heq (coherentEdgeHom_heq
    (ConcreteCategory.congr_hom ((SimplicialNerve C).δ_comp_δ_self (i := (0 : Fin 3))) s).symm)
/-- 概要：四面に現れる辺 01 の二つの表示は同じ射。
方針：単体恒等式と辺の読み戻しの関手性を使う。
規約：同型に弱めず射自体を同定する。
使われ方：四つの三角形の関手同型の両端を同時に揃える。 -/
lemma coherentTetrahedronBoundary01 (s : (SimplicialNerve C) _⦋3⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 2 ((SimplicialNerve C).δ 3 s)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 2 ((SimplicialNerve C).δ 2 s)) := by
  exact eq_of_heq (coherentEdgeHom_heq
    (ConcreteCategory.congr_hom ((SimplicialNerve C).δ_comp_δ_self (i := (2 : Fin 3))) s).symm)
/-- 概要：四面に現れる辺 12 の二つの表示は同じ射。
方針：単体恒等式と辺の読み戻しの関手性を使う。
規約：同型に弱めず射自体を同定する。
使われ方：四つの三角形の関手同型の両端を同時に揃える。 -/
lemma coherentTetrahedronBoundary12 (s : (SimplicialNerve C) _⦋3⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 0 ((SimplicialNerve C).δ 3 s)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 2 ((SimplicialNerve C).δ 0 s)) := by
  exact eq_of_heq (coherentEdgeHom_heq
    (ConcreteCategory.congr_hom
      ((SimplicialNerve C).δ_comp_δ (show (0 : Fin 3) ≤ 2 by decide)) s))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
