module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorTranspose
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFiberCocone
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeConeFamilies

/-!
概要：相対 join の fiber への制限と図式の族の転置・頂点評価との整合性。
方針：転置の前合成の自然性と二重転置を使い、関手の頂点の全単射で照合する。
規約：単体集合と図式は任意。
使われ方：境界の最初の大域図式の局所余極限性を局所余錐の族へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：fiber の余錐を転置した族の頂点は、元の大域図式の同じ頂点の fiber の余錐。
方針：fiber の制限を転置後の関手の制限へ移し、二重転置と頂点の全単射を使う。
規約：余錐の値の厳密な等式であり、図式の型の相違を許す。
使われ方：最初の境界頂点の余極限条件を局所の境界充填の入力へ変換する。 -/
lemma kanRelativeJoinFiberCocone_transpose_familyAt_val {K C A D : SSet.{u}}
    (p : K ⟶ C) (c : C _⦋0⦌)
    (a : A ⟶ (ihom (relativeJoin p (𝟙 C))).obj D) (x : A _⦋0⦌) :
    (kanCoconeFamilyAt
      (SerrePositivity.InfinityCategories.F1B.functorTranspose (kanRelativeJoinFiberCocone p c (SerrePositivity.InfinityCategories.F1B.functorTranspose a)).val) x).val =
      (kanRelativeJoinFiberCocone p c
        ((functorVertexEquiv (relativeJoin p (𝟙 C)) D).symm (a.app (Opposite.op ⦋0⦌) x))).val := by
  apply functorVertex_injective
  rw [kanCoconeFamilyAt_vertex]
  change (SerrePositivity.InfinityCategories.F1B.functorTranspose (((kanRelativeJoinBaseFiberIso p c).hom ≫
    vertexFiberι (relativeJoinBaseProjection p (𝟙 C)) c) ≫ SerrePositivity.InfinityCategories.F1B.functorTranspose a)).app
      (Opposite.op ⦋0⦌) x = functorVertex _
  rw [SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left, SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose]
  have h := (functorVertexEquiv (relativeJoin p (𝟙 C)) D).apply_symm_apply
    (a.app (Opposite.op ⦋0⦌) x)
  change functorVertex _ = a.app (Opposite.op ⦋0⦌) x at h
  have hh := congrArg (fun y ↦
    ((pre ((kanRelativeJoinBaseFiberIso p c).hom ≫
      vertexFiberι (relativeJoinBaseProjection p (𝟙 C)) c)).app D).app (Opposite.op ⦋0⦌) y) h.symm
  exact hh

end SerrePositivity.InfinityCategories.F1B
