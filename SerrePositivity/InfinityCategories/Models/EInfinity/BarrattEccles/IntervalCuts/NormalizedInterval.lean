module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Values
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.BoundaryCuts
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Data.Finset.Sort

/-!
模型。文献の定義との比較は後で
# 標準一単体の実際の正規化区間

概要：Berger–Fresse §2.2 の出力単体を N_*(Δ¹) の正規化生成元へ送る。
方針：非空頂点集合を昇順に列挙し、既存の正規化鎖関手を直接使う。
規約：補助の同型な複体を仮定せず、鎖次数 q をコチェイン次数 −q に置く。
使われ方：区間切断の有限和を実際の区間テンソルの成分へ接続する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：頂点集合を昇順に並べる単調埋め込み（BF §2.2.1）。
方針：有限集合の順序付き列挙を使う。
規約：定義域の大きさは単体次数+1。
使われ方：切断の出力を標準一単体の面として表す。 -/
def simplexEmbedding (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s + 1) ↪o Fin 2 :=
  s.val.orderEmbOfFin (by
    have := Finset.card_pos.mpr s.property
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree
    omega)

/-- 概要：非空頂点集合が指定する Δ¹ の非退化単体（BF §2.2.1）。
方針：昇順の頂点埋め込みを標準単体の単体へ送る。
規約：零・一・辺を同じ定義で扱う。
使われ方：切断の出力基底の正規化生成元。 -/
def faceSimplex (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) : Δ[1] _⦋_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s⦌ :=
  SSet.stdSimplex.objMk (n := ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexEmbedding s).toOrderHom

/-- 概要：標準一単体の頂点 b（BF §2.2.1）。
方針：定数な零次単体を取る。
規約：b は零または一。
使われ方：区間の端点と辺の境界。 -/
def vertexSimplex (b : Fin 2) : Δ[1] _⦋0⦌ :=
  SSet.stdSimplex.objMk (OrderHom.const (Fin 1) b)

/-- 概要：標準一単体の向き付き辺（BF §2.2.1）。
方針：単体圏の恒等射を表現単体として読む。
規約：向きは零から一。
使われ方：区間の一次生成元。 -/
def edgeSimplex : Δ[1] _⦋1⦌ := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)

/-- 概要：一点集合の面は指定した頂点単体（BF §2.2.1）。
方針：順序付き列挙の値が一元集合に属することを使う。
規約：単体次数は零。
使われ方：面の一般生成元を端点生成元へ同定する。 -/
lemma faceSimplex_vertex (b : Fin 2) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceSimplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexSimplex b := by
  apply SSet.stdSimplex.ext
  intro i
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexEmbedding (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) i = b
  exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ i)

/-- 概要：二頂点全体の面は恒等辺単体（BF §2.2.1）。
方針：昇順の二頂点の列挙を各位置で計算する。
規約：向きは零から一。
使われ方：面の一般生成元を辺生成元へ同定する。 -/
lemma faceSimplex_edge : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceSimplex _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex := by
  apply SSet.stdSimplex.ext
  intro i
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexEmbedding _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge i = i
  have h : (fun j : Fin 2 => j) =
      (Finset.univ : Finset (Fin 2)).orderEmbOfFin (by decide) :=
    Finset.orderEmbOfFin_unique _ (fun j => Finset.mem_univ j) (fun _ _ hj => hj)
  exact (congrFun h i).symm

variable (A : Type u) [CommRing A]

/-- 概要：実際の標準一単体の正規化鎖（BF §2.1–2.2）。
方針：自由単体加群の正規化 Moore 複体を取る。
規約：自然数の鎖次数。
使われ方：区間切断の出力の基礎となる鎖複体。 -/
abbrev intervalChains := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Δ[1]

/-- 概要：実際の N_*(Δ¹) の整数コチェイン表示（BF §2.1–2.2）。
方針：既存の正規化関手を標準一単体へ適用する。
規約：鎖次数 q は整数次数 −q。
使われ方：具体的な E-coalgebra 区間の底の複体。 -/
def interval : Complex A := (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj Δ[1]

/-- 概要：区間の負整数成分と自然数鎖成分の比較（BF §2.1）。
方針：次数延長の標準同型を使う。
規約：符号や生成元は変更しない。
使われ方：切断の鎖次数の計算を整数テンソルへ移す。 -/
def intervalXIso (q : ℕ) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X (-(q : ℤ)) ≅ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A).X q :=
  extendXIso _ ComplexShape.embeddingDownNat rfl

/-- 概要：切断の出力単体が定める実際の正規化鎖（BF §2.2.6）。
方針：標準一単体の面へ正規化射影を適用する。
規約：成分はその面の鎖次数。
使われ方：有限な出力基底を N_*(Δ¹) へ送る。 -/
def faceChain (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A).X (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s) :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Δ[1] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceSimplex s)

/-- 概要：切断の出力単体の整数複体の生成元（BF §2.2.6）。
方針：正規化鎖の生成元を次数延長の同型で戻す。
規約：整数次数は単体次数の負。
使われ方：区間の反復テンソルの生成元。 -/
def faceVector (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ)) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s)).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain A s)

/-- 概要：区間の零次の端点生成元（BF §2.1）。
方針：頂点単体を正規化する。
規約：b は零・一のどちらでもよい。
使われ方：辺の微分と端点射の計算。 -/
def vertexChain (b : Fin 2) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A).X 0 :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Δ[1] 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexSimplex b)

/-- 概要：区間の一次の辺生成元（BF §2.1）。
方針：恒等一単体を正規化する。
規約：零から一への向きを保つ。
使われ方：区間の微分と切断の入力生成元。 -/
def edgeChain : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A).X 1 :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Δ[1] 1 _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex

/-- 概要：一点集合の正規化面生成元は端点生成元（BF §2.2.1）。
方針：対応する単体の一致を正規化生成元へ渡す。
規約：鎖次数零。
使われ方：区間の端点の切断作用の比較。 -/
lemma faceChain_vertex (b : Fin 2) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A b := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceSimplex_vertex]
  rfl

/-- 概要：全頂点集合の正規化面生成元は辺生成元（BF §2.2.1）。
方針：面単体と恒等辺単体の一致を使う。
規約：鎖次数一。
使われ方：区間の辺の切断作用の比較。 -/
lemma faceChain_edge : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceSimplex_edge]
  rfl

/-- 概要：辺の最初の面は終点（BF §2.1）。
方針：標準単体の零番面を各頂点で評価する。
規約：δ₀ は零番頂点を削除する。
使われ方：正規化された辺の境界の符号。 -/
lemma edgeSimplex_face_zero : (Δ[1] : SSet).δ (0 : Fin 2) _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexSimplex 1 := by
  ext i
  fin_cases i
  rfl

/-- 概要：辺の最後の面は始点（BF §2.1）。
方針：標準単体の一番面を各頂点で評価する。
規約：δ₁ は一番頂点を削除する。
使われ方：正規化された辺の境界の符号。 -/
lemma edgeSimplex_face_one : (Δ[1] : SSet).δ (1 : Fin 2) _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexSimplex 0 := by
  ext i
  fin_cases i
  rfl

/-- 概要：実際の正規化区間の辺の微分は終点−始点（BF §2.1）。
方針：一般の正規化生成元の境界公式を二つの面へ展開する。
規約：鎖次数一から零への微分。
使われ方：区間切断の微分保存を入力の辺で検証する。 -/
lemma edgeChain_d : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A).d 1 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A 1 - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_d]
  simp [Fin.sum_univ_two, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex_face_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex_face_one, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain, sub_eq_add_neg]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
