module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LowDimensional
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-! # 任意の dg 圏の dg nerve

概要：HA の部分集合による単体と単調写像の引き戻しを単体的集合にする。
方針：引き戻しの恒等・合成の法則から反変関手を構成する。
規約：HA Construction 1.3.1.6、cochain 次数 `2-|I|`、宇宙は `max u v`。
使われ方：quasicategory・H⁰ 比較・右 pinched 写像空間の共通の入口。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 概要：任意の dg 圏の dg nerve は部分集合で添字付けた単体の単体的集合。
方針：任意の単調写像に沿う引き戻しを使い、恒等・合成の法則を成分ごとに確認する。
規約：HA Construction 1.3.1.6、対象宇宙 v と Hom 宇宙 u は独立。
使われ方：導来 ∞ 圏の定義の基盤。quasicategory 性は後続で証明する。 -/
@[kerodon 00PQ]
def dgNerve : SSet.{max u v} where
  obj Δ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D Δ.unop.len
  map f := ↾fun s => s.pullback f.unop.toOrderHom
  map_id _ := by
    ext s
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_id s
  map_comp f g := by
    ext s
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp s g.unop.toOrderHom f.unop.toOrderHom).symm

namespace dgNerve

/-- 概要：dg nerve の n 単体の型は HA の方程式を持つ単体の型。
方針：定義の評価。規約：HA Construction 1.3.1.6。
使われ方：単体のデータの accessor への接続。 -/
lemma obj (n : ℕ) : (dgNerve A D) _⦋n⦌ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n := rfl

/-- 概要：dg nerve の零単体は元の dg 圏の対象と同値。
方針：唯一の頂点で評価する既存の同値を使う。
規約：HA Example 1.3.1.8。使われ方：頂点を固定する写像空間と H⁰ 比較。 -/
def vertexEquiv : (dgNerve A D) _⦋0⦌ ≃ D := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv

/-- 概要：dg nerve の一単体は二頂点とその間の閉次数零元と同値。
方針：辺の同値を単体的集合の各次数に読み替える。
規約：HA Example 1.3.1.8。使われ方：辺と閉零圏の射の同定。 -/
def edgeEquiv : (dgNerve A D) _⦋1⦌ ≃
    Σ obj : Fin 2 → D, zeroCycles (homObject A D (obj 0) (obj 1)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv

/-- 概要：面写像は対応する頂点を飛ばす。
方針：単体的集合と引き戻しの定義の評価。
規約：HA Construction 1.3.1.6、Mathlib の面の番号。使われ方：ホーンの面の比較。 -/
lemma δ_obj {n : ℕ} (i : Fin (n + 2)) (s : (dgNerve A D) _⦋n + 1⦌)
    (j : Fin (n + 1)) : ((dgNerve A D).δ i s).obj j = s.obj (i.succAbove j) := rfl

/-- 概要：退化写像は対応する頂点を重複させる。
方針：単体的集合と引き戻しの定義の評価。
規約：HA Construction 1.3.1.6、Mathlib の退化の番号。使われ方：退化辺と高次成分の比較。 -/
lemma σ_obj {n : ℕ} (i : Fin (n + 1)) (s : (dgNerve A D) _⦋n⦌)
    (j : Fin (n + 2)) : ((dgNerve A D).σ i s).obj j = s.obj (i.predAbove j) := rfl

end dgNerve

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.1.6"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve
attribute [cite HA "1.3.1.8"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.edgeEquiv
attribute [cite HA "1.3.1.8"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv
attribute [cite HA "1.3.2.2" (partial := special) "仮定：可換環上の dg 圏または加群複体（Lean が強い：任意の加法圏ではない）。結論：dg nerve の辺を閉次数 0 射と同定し、h の Hom を H⁰ と比べ、具体的な鎖写像を辺に対応させる（加群複体で一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.edgeEquiv
