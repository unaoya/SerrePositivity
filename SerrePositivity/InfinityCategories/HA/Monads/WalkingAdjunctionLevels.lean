module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionVertices
public import Mathlib.Algebra.BigOperators.Fin

/-!
概要：全次元のwalking adjunctionの射の圏と、その分解で使う有限の長さを構成する。
方針：各Homのn単体を有限順序集合からの実関手で表す。
規約：零次元に切り詰めない。全水平合成と長さの加法則を同時に保持する。
使われ方：Riehl–Verity Proposition 3.1.10・Theorem 4.3.9、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の全coherenceの構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped BigOperators

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：n次元の射を持つ圏の二つの対象。
方針：各次数に同じ二点を置く。規約：次数を型に保持する。
使われ方：Riehl–Verity Proposition 3.1.10 の各次数の自由な圏。 -/
structure WalkingAdjunctionLevel (n : ℕ) where
  point : WalkingAdjunctionPoint

/-- 概要：全随伴のn単体を射とする実圏。
方針：有限順序集合からHom圏への全関手を使い、水平合成の全法則を適用する。
規約：合成は全n単体上に定義する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
instance walkingAdjunctionLevelCategory (n : ℕ) : Category (WalkingAdjunctionLevel n) where
  Hom X Y := Fin (n + 1) ⥤ walkingAdjunctionHom X.point Y.point
  id X := (Functor.const _).obj (walkingAdjunctionIdentity X.point)
  comp {X Y Z} F G := F.prod' G ⋙ walkingAdjunctionHorizontal X.point Y.point Z.point
  id_comp {X Y} F := walkingAdjunctionHorizontal_leftUnit X.point Y.point F
  comp_id {X Y} F := walkingAdjunctionHorizontal_rightUnit X.point Y.point F
  assoc {W X Y Z} F G H :=
    walkingAdjunctionHorizontal_assoc W.point X.point Y.point Z.point F G H

/-- 概要：全単体の有限の長さ。
方針：各頂点の生成語の長さを全頂点について足す。
規約：高次の射の分解の停止に使い、退化を除去した次元とは区別する。
使われ方：Riehl–Verity Proposition 3.1.10 の原子的な射への分解。 -/
def walkingAdjunctionLevelSize {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) : ℕ :=
  ∑ i : Fin (n + 1), walkingAdjunctionVertexLength X Y (F.obj i)

/-- 概要：n次元の単位の長さは0。
方針：全頂点が長さ0の単位であることを使う。
規約：同じ単位の定値関手。使われ方：Riehl–Verity Proposition 3.1.10 の空の分解。 -/
lemma walkingAdjunctionLevelSize_id (n : ℕ) (X : WalkingAdjunctionPoint) :
    walkingAdjunctionLevelSize
      ((Functor.const (Fin (n + 1))).obj (walkingAdjunctionIdentity X)) = 0 := by
  simp only [walkingAdjunctionLevelSize, Functor.const_obj_obj,
    walkingAdjunctionVertexLength_id, Finset.sum_const_zero]

/-- 概要：全水平合成のn次元の長さは加法的。
方針：各頂点の長さの加法則を足し合わせる。
規約：全八合成。使われ方：Riehl–Verity Proposition 3.1.10 の分解の停止。 -/
lemma walkingAdjunctionLevelSize_comp {n : ℕ} (X Y Z : WalkingAdjunctionPoint)
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (G : Fin (n + 1) ⥤ walkingAdjunctionHom Y Z) :
    walkingAdjunctionLevelSize (F.prod' G ⋙ walkingAdjunctionHorizontal X Y Z) =
      walkingAdjunctionLevelSize F + walkingAdjunctionLevelSize G := by
  simp only [walkingAdjunctionLevelSize, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.prod'_obj, walkingAdjunctionVertexLength_comp, Finset.sum_add_distrib]

/-- 概要：全単体の長さ0から各頂点の長さ0を回収する。
方針：自然数の有限和が0となる条件を使う。
規約：全ての頂点。使われ方：Riehl–Verity Proposition 3.1.10 の単位の検出。 -/
lemma walkingAdjunctionLevelSize_vertex_zero {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (h : walkingAdjunctionLevelSize F = 0)
    (i : Fin (n + 1)) : walkingAdjunctionVertexLength X Y (F.obj i) = 0 := by
  exact (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)

/-- 概要：長さ0の全単体は自己Homにある。
方針：異なる二点の間の頂点の長さは奇数であることを使う。
規約：全次数で少なくとも一つの頂点がある。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionLevelSize_zero_endpoints {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (h : walkingAdjunctionLevelSize F = 0) :
    X = Y := by
  have h₀ := walkingAdjunctionLevelSize_vertex_zero F h 0
  cases X <;> cases Y
  · rfl
  · simp only [walkingAdjunctionVertexLength] at h₀; omega
  · simp only [walkingAdjunctionVertexLength] at h₀; omega
  · rfl

/-- 概要：単位の対象の自己射は一つだけ。
方針：空の自己Homを場合分けする。規約：実Hom圏内の射。
使われ方：Riehl–Verity Proposition 3.1.10 の長さ0の全単体の検出。 -/
instance walkingAdjunctionIdentityHom_subsingleton (X : WalkingAdjunctionPoint) :
    Subsingleton (walkingAdjunctionIdentity X ⟶ walkingAdjunctionIdentity X) := by
  cases X <;> dsimp [walkingAdjunctionIdentity, walkingAdjunctionHom] <;> infer_instance

/-- 概要：自己Homの全単体は長さ0なら単位そのものである。
方針：頂点の長さの単射性と単位の自己射の一意性を使う。
規約：対象だけでなく全関手の等式。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionLevelSize_zero_eq_id {n : ℕ} {X : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X X) (h : walkingAdjunctionLevelSize F = 0) :
    F = (Functor.const _).obj (walkingAdjunctionIdentity X) := by
  have ho (i : Fin (n + 1)) : F.obj i = walkingAdjunctionIdentity X := by
    apply walkingAdjunctionVertexLength_injective X X
    rw [walkingAdjunctionLevelSize_vertex_zero F h i, walkingAdjunctionVertexLength_id]
  refine CategoryTheory.Functor.ext ho ?_
  intro i j f
  have : Subsingleton (F.obj i ⟶ F.obj j) := by
    rw [ho i, ho j]
    infer_instance
  exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.HA.Monads
