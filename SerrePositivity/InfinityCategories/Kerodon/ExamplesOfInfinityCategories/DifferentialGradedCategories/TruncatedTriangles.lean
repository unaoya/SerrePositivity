module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TruncatedEdges

/-! # 端点付きの三角形と合成の差の原始元

概要：Mathlib の三角形の合成構造を、閉零射の合成と第三辺の差を埋める射と比較する。
方針：三角形の三つの面の計算と、dg nerve の二単体の既存の特徴づけを使う。
規約：HA Example 1.3.1.8、Kerodon §2.5.3（Tag 00PK）。使われ方：辺のホモトピーと H⁰ の境界関係の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open CategoryTheory.SimplicialObject.Truncated
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：三対象から三角形の対象族を作る。
方針：最初の対象と残り二対象の族を有限型の分岐でつなぐ。
規約：HA Example 1.3.1.8。使われ方：原始元から三角形を構成する対象族。 -/
def tripleObj (x y z : D) : Fin 3 → D := Fin.cases x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj y z)

/-- 概要：三角形から作った二単体の第 2 面は辺 0→1 の一単体。
方針：一単体の対象族と閉零成分の同値で比較する。
規約：HA Example 1.3.1.8。使われ方：合成構造の最初の辺の確認。 -/
lemma triangle_face01 (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData A D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj (t.obj 0) (t.obj 1)) t.f01 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  apply Sigma.ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl

/-- 概要：三角形から作った二単体の第 0 面は辺 1→2 の一単体。
方針：一単体の対象族と閉零成分の同値で比較する。
規約：HA Example 1.3.1.8。使われ方：合成構造の二番目の辺の確認。 -/
lemma triangle_face12 (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData A D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj (t.obj 1) (t.obj 2)) t.f12 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  apply Sigma.ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl

/-- 概要：三角形から作った二単体の第 1 面は辺 0→2 の一単体。
方針：一単体の対象族と閉零成分の同値で比較する。
規約：HA Example 1.3.1.8。使われ方：合成構造の対角辺の確認。 -/
lemma triangle_face02 (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData A D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj (t.obj 0) (t.obj 2)) t.f02 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  apply Sigma.ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl

/-- 概要：三辺の合成の差を埋める次数 −1 の射から、端点付きの合成構造を構成する。
方針：対応する三角形データから二単体を作り、三つの面の計算を使う。
規約：HA Example 1.3.1.8。使われ方：境界関係から辺のホモトピーを作る。 -/
def compStructOfHomotopy {x y z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    (f : SSet.Truncated.Edge x y) (g : SSet.Truncated.Edge y z) (h : SSet.Truncated.Edge x z)
    (t : GradedHom A (x.obj 0) (z.obj 0) (-1))
    (ht : differential A t = compose A (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle g).val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle f).val (by decide) -
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle h).val) : SSet.Truncated.Edge.CompStruct f g h := by
  let T : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData A D :=
    { obj := tripleObj (x.obj 0) (y.obj 0) (z.obj 0)
      f01 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle f
      f12 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle g
      f02 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle h
      homotopy := t
      differential_homotopy := ht }
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle T, ?_, ?_, ?_⟩
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle T) = f.edge
    rw [triangle_face01]
    exact congrArg SSet.Truncated.Edge.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle_edgeCycle f)
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle T) = g.edge
    rw [triangle_face12]
    exact congrArg SSet.Truncated.Edge.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle_edgeCycle g)
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle T) = h.edge
    rw [triangle_face02]
    exact congrArg SSet.Truncated.Edge.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle_edgeCycle h)

/-- 概要：端点付きの合成構造から、三辺の合成と対角辺の差の原始元が得られる。
方針：面と端点の等式を消去し、二単体の微分方程式を適用する。
規約：HA Example 1.3.1.8。使われ方：辺のホモトピーから境界関係を導く。 -/
lemma homotopy_of_compStruct {x y z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    {f : SSet.Truncated.Edge x y} {g : SSet.Truncated.Edge y z} {h : SSet.Truncated.Edge x z}
    (c : SSet.Truncated.Edge.CompStruct f g h) :
    ∃ t : GradedHom A (x.obj 0) (z.obj 0) (-1),
      differential A t = compose A (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle g).val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle f).val (by decide) -
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle h).val := by
  rcases f with ⟨f, fs, ft⟩
  rcases g with ⟨g, gs, gt⟩
  rcases h with ⟨h, hs, ht⟩
  rcases c with ⟨s, d2, d0, d1⟩
  cases d2
  cases d0
  cases d1
  cases fs
  cases ft
  cases gt
  refine ⟨s.triangleHom, ?_⟩
  exact s.differential_triangleHom

/-- 概要：合成構造の存在は、三辺の合成と対角辺の差が次数 −1 の境界であることと同値。
方針：合成構造と原始元の間の二つの構成を使う。
規約：HA Example 1.3.1.8、Kerodon §2.5.3（Tag 00PK）。使われ方：ホモトピーと合成の判定。 -/
lemma compStruct_iff_homotopy {x y z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    (f : SSet.Truncated.Edge x y) (g : SSet.Truncated.Edge y z) (h : SSet.Truncated.Edge x z) :
    Nonempty (SSet.Truncated.Edge.CompStruct f g h) ↔
      ∃ t : GradedHom A (x.obj 0) (z.obj 0) (-1),
        differential A t = compose A (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle g).val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle f).val (by decide) -
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle h).val :=
  ⟨fun ⟨c⟩ => homotopy_of_compStruct c, fun ⟨t, ht⟩ => ⟨compStructOfHomotopy f g h t ht⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
