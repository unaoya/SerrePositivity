module
public import SerrePositivity.InfinityCategories.PinchedHom.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-! # 右 pinched Hom の頂点と元の辺

概要：右 pinched Hom の零単体は元の単体的集合の端点付き辺と同じデータを持つ。
方針：零次の先頭面と最終頂点を二つの面写像に同定する。
規約：Kerodon §4.6.5。使われ方：dg nerve の閉零射との比較の入口。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.PinchedHom

open CategoryTheory Opposite
open scoped Simplicial

variable {X : SSet.{u}} (x y : X _⦋0⦌)

/-- 概要：零次の定値単体はその零単体自身。
方針：零単体への唯一の射が恒等射であることを使う。
規約：Kerodon §4.6.5。使われ方：始点条件の通常の面による表現。 -/
lemma constant_zero : constant x 0 = x := by
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  unfold constant
  rw [h]
  exact X.map_id_apply _ x

/-- 概要：右 pinched Hom の零単体と元の端点付き辺の同値。
方針：元の一単体を保ち、二つの端点条件を面の等式に読み替える。
規約：Kerodon §4.6.5。使われ方：dg nerve の閉次数零元への同定。 -/
def vertexEquiv : (pinchedHom x y) _⦋0⦌ ≃ X.Edge x y where
  toFun s := SSet.Edge.mk s.val
    (by simpa only [front_zero, constant_zero, SimplicialObject.δ] using s.source)
    (by simpa only [lastVertex_zero, SimplicialObject.δ] using s.target)
  invFun e :=
    { val := e.edge
      source := by simpa only [front_zero, constant_zero, SimplicialObject.δ] using e.src_eq
      target := by simpa only [lastVertex_zero, SimplicialObject.δ] using e.tgt_eq }
  left_inv s := Simplex.ext rfl
  right_inv e := SSet.Edge.ext rfl

/-- 概要：頂点と辺の同値は元の一単体を変えない。
方針：同値の順写像を評価する。
規約：Kerodon §4.6.5。使われ方：斉次成分の評価の比較。 -/
lemma vertexEquiv_edge (s : (pinchedHom x y) _⦋0⦌) :
    (vertexEquiv x y s).edge = s.val := rfl

end SerrePositivity.InfinityCategories.PinchedHom
