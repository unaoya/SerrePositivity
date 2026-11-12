module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Quasicategory
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Triangle
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory

/-! # dg nerve の二次切断の辺と閉零射

概要：二次切断の端点を固定した辺は、その対象間の閉次数零射と同じ情報を持つ。
方針：零単体と対象の同値および一単体の既存の特徴づけを、端点の等式で移送する。
規約：HA Example 1.3.1.8、Kerodon §2.5.3（Tag 00PK）。使われ方：ホモトピー圏と H⁰ 圏の射の比較。

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

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 概要：dg nerve の二次切断。
方針：Mathlib の切断関手を適用する。
規約：HA Proposition 1.3.1.10。使われ方：二次切断のホモトピー圏の比較。 -/
abbrev twoTruncation := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

variable {A D}

/-- 概要：二つの対象から辺の対象族を作る。
方針：有限二点型の最初と最後に指定対象を置く。
規約：HA Example 1.3.1.8。使われ方：閉零射から一単体を構成する対象族。 -/
def pairObj (x y : D) : Fin 2 → D := Fin.cases x (fun _ => y)

/-- 概要：端点付きの辺の始点の対象は、一単体の最初の対象に一致する。
方針：辺の始点の面の等式を、零単体の対象で評価する。
規約：HA Example 1.3.1.8。使われ方：辺を閉零射へ送る始点の移送。 -/
lemma edge_source_obj {x y : (twoTruncation A D) _⦋0⦌₂}
    (e : SSet.Truncated.Edge x y) : e.edge.obj 0 = x.obj 0 :=
  congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 0 => s.obj 0) e.src_eq

/-- 概要：端点付きの辺の終点の対象は、一単体の最後の対象に一致する。
方針：辺の終点の面の等式を、零単体の対象で評価する。
規約：HA Example 1.3.1.8。使われ方：辺を閉零射へ送る終点の移送。 -/
lemma edge_target_obj {x y : (twoTruncation A D) _⦋0⦌₂}
    (e : SSet.Truncated.Edge x y) : e.edge.obj 1 = y.obj 0 :=
  congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 0 => s.obj 0) e.tgt_eq

/-- 概要：端点付きの辺は両端の対象間の閉次数零射を定める。
方針：一単体の閉零成分を取り、端点の対象の等式で移送する。
規約：HA Example 1.3.1.8。使われ方：ホモトピー圏から H⁰ への比較写像。 -/
def edgeCycle {x y : (twoTruncation A D) _⦋0⦌₂} (e : SSet.Truncated.Edge x y) :
    zeroCycles (homObject A D (x.obj 0) (y.obj 0)) :=
  cast (by rw [edge_source_obj e, edge_target_obj e]) (e.edge.edgeCycle 0 1 (by decide))

/-- 概要：両端の対象間の閉零射から端点を固定した辺を構成する。
方針：二頂点の対象族を作り、閉零射から一単体を構成し、その両端の面を同定する。
規約：HA Example 1.3.1.8。使われ方：H⁰ からホモトピー圏へ送る辺の代表元。 -/
def edgeOfCycle {x y : (twoTruncation A D) _⦋0⦌₂}
    (f : zeroCycles (homObject A D (x.obj 0) (y.obj 0))) : SSet.Truncated.Edge x y where
  edge := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (pairObj (x.obj 0) (y.obj 0)) f
  src_eq := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
    rfl
  tgt_eq := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
    rfl

/-- 概要：閉零射から作った辺の閉零成分は元に戻る。
方針：一単体の成分の構成を評価し、反射律による移送を消す。
規約：HA Example 1.3.1.8。使われ方：端点固定の辺の同値の片側の逆。 -/
lemma edgeCycle_edgeOfCycle {x y : (twoTruncation A D) _⦋0⦌₂}
    (f : zeroCycles (homObject A D (x.obj 0) (y.obj 0))) : edgeCycle (edgeOfCycle f) = f := by
  rfl

/-- 概要：端点付きの辺を閉零成分から再構成すると元に戻る。
方針：端点の面の等式を消去し、二頂点の対象族と一単体の再構成を使う。
規約：HA Example 1.3.1.8。使われ方：端点固定の辺の同値のもう片側の逆。 -/
lemma edgeOfCycle_edgeCycle {x y : (twoTruncation A D) _⦋0⦌₂}
    (e : SSet.Truncated.Edge x y) : edgeOfCycle (edgeCycle e) = e := by
  rcases e with ⟨s, hs, ht⟩
  cases hs
  cases ht
  apply SSet.Truncated.Edge.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (pairObj (s.obj 0) (s.obj 1))
    (s.edgeCycle 0 1 (by decide)) = s
  have hobj : pairObj (s.obj 0) (s.obj 1) = s.obj := by
    funext i
    fin_cases i <;> rfl
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  exact Sigma.ext hobj (heq_of_eq rfl)

/-- 概要：固定した二頂点の間の辺と、その対象間の閉次数零射は同値。
方針：辺の閉零成分の評価と閉零射からの辺の構成を互いに逆として組み合わせる。
規約：HA Example 1.3.1.8、Kerodon §2.5.3（Tag 00PK）。使われ方：ホモトピー類による商の比較。 -/
def edgeCycleEquiv (x y : (twoTruncation A D) _⦋0⦌₂) :
    SSet.Truncated.Edge x y ≃ zeroCycles (homObject A D (x.obj 0) (y.obj 0)) where
  toFun := edgeCycle
  invFun := edgeOfCycle
  left_inv := edgeOfCycle_edgeCycle
  right_inv := edgeCycle_edgeOfCycle

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
