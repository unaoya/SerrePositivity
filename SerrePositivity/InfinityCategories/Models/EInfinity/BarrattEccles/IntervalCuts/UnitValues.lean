module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CochainAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorDegreeTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComplexUnit
public import SerrePositivity.EInfinity.BarrattEccles.Unitors

/-!
模型。文献の定義との比較は後で
# 一文字単位の区間切断値

概要：Berger–Fresse §2.2.6 の一文字語の余演算を区間の恒等演算へ比較する。
方針：唯一の切断を評価し、一次テンソル冪の右単位子の逆へ同定する。
規約：実際の整数区間と全ての可換係数環を扱う。
使われ方：χ の区間余演算の単位則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：一因子の指定次数テンソルは右単位子の逆による面生成元（BF §2.2.6）。
方針：テンソル生成元の再帰式と複体の右単位子の公式を使う。
規約：指定次数は面の鎖次数。
使われ方：単位語の出力を元の区間へ戻す。 -/
lemma tensorVectorOfDegree_one (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A 1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s) (fun _ => s)
      (by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree]) =
      (oneIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).inv.f (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A s) := by
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A 1 (fun _ => s) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ))
    (by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree]) = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_succ A 0 _ _ 0 _ rfl (by rfl) (add_zero _)]
  simp only [eqToHom_refl, ModuleCat.id_apply]
  exact (_root_.SerrePositivity.EInfinity.BarrattEccles.cochain_rightUnitor_inv_apply A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)
    (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A s)).symm

/-- 概要：一文字単位語の唯一の辺切断は非退化（BF §2.2.1）。
方針：二つの展開頂点の色と値を有限に判定する。
規約：単位語は恒等置換の一文字語。
使われ方：辺の切断和の唯一の項。 -/
lemma unitWord_edgeNondegenerate :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 1))).val 0 := by decide

/-- 概要：一文字単位語の辺切断の出力は元の辺（BF §2.2.1）。
方針：唯一の色の出力頂点集合を計算する。
規約：全出力族は一因子。
使われ方：単位の辺成分の値を同定する。 -/
lemma unitWord_edgeOutput :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 1))) 0 = (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) := by
  funext k
  fin_cases k
  apply Subtype.ext
  decide

/-- 概要：一文字単位語の辺切断符号は正（BF §2.2.4）。
方針：逆転も内側区間もないことを有限に計算する。
規約：符号は整数。
使われ方：単位の辺成分のスカラーを消す。 -/
lemma unitWord_edgeSign :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 1))).val 0 = 1 := by decide

/-- 概要：χ の単位元の辺成分は右単位子の逆である（BF §2.2.6）。
方針：一文字基底の唯一の切断を評価する。
規約：区間の次数 −1 成分。
使われ方：辺入力での複体射の単位則。 -/
lemma edgeComponent_unitElement :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent A 1 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.unitElement A) =
      (oneIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).inv.f (-1) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 1).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.unitElement, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent_basis]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord
  rw [Fin.sum_univ_one, dite_eq_left _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unitWord_edgeNondegenerate, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unitWord_edgeSign]
  simp only [Int.cast_one, one_smul]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unitWord_edgeOutput]
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_edge, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain_edge] using!
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree_one A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge

/-- 概要：χ の単位元の頂点成分は右単位子の逆である（BF §2.2.6）。
方針：零語次数の頂点成分と一因子テンソル公式を使う。
規約：両端点を同時に扱う。
使われ方：頂点入力での複体射の単位則。 -/
lemma vertexComponent_unitElement (b : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A 1 0 b (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.unitElement A) =
      (oneIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).inv.f 0 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A b)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.unitElement, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_basis]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord
  rw [dite_eq_left rfl]
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_vertex, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain_vertex] using!
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree_one A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
