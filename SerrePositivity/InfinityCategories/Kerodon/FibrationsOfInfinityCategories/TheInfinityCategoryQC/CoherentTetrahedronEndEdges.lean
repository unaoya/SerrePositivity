module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronLastFace

/-!
概要：三単体の始端と終端の固定射の回収。
方針：path の像と豊穣 Hom から core Fun への包含を計算する。
規約：元の一単体とそのホモトピー類を保持する。
使われ方：Cat_∞ の引き戻し錐の指定可換性の照合。

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
/-- 概要：始端の固定 path の像は元の辺 01 の豊穣頂点。
方針：辺の読み戻しの全単射の逆写像の式を使う。
規約：元の三単体の辺を保つ。
使われ方：四面の合成則の固定射を実際の関手へ移す。 -/
lemma coherentTetrahedronPath01_image (s : (SimplicialNerve C) _⦋3⦌) :
    (s.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath01) =
      SimplicialCategory.homEquiv' _ _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 2 ((SimplicialNerve C).δ 2 s))) := by
  exact ((SimplicialCategory.homEquiv' _ _).apply_symm_apply _).symm
/-- 概要：終端の固定 path の像は元の辺 23 の豊穣頂点。
方針：辺の読み戻しの全単射の逆写像の式を使う。
規約：元の三単体の辺を保つ。
使われ方：四面の合成則の固定射を実際の関手へ移す。 -/
lemma coherentTetrahedronPath23_image (s : (SimplicialNerve C) _⦋3⦌) :
    (s.map ⟨ULift.up 2⟩ ⟨ULift.up 3⟩).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath23) =
      SimplicialCategory.homEquiv' _ _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom ((SimplicialNerve C).δ 0 ((SimplicialNerve C).δ 1 s))) := by
  exact ((SimplicialCategory.homEquiv' _ _).apply_symm_apply _).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
