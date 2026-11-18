module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ContractionHomotopy

/-!
模型。文献の定義との比較は後で
# 三生成元で指定した区間射の全整数成分

概要：Berger–Fresse §3.1・Berger–Moerdijk 命題 4.1 の境界持ち上げで区間射を作る。
方針：両頂点と辺の像を零次・−1 次で線形延長し、他次数を零にする。
規約：標的は任意の非有界整数複体。
使われ方：指定した両端点と境界を持つ辺から実際の区間射を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：頂点線形延長を実際の面生成元で評価する（BF §3.1）。
方針：面表示と正規化鎖表示の一致を既存の評価へ送る。
規約：標的は任意の係数加群。
使われ方：区間射の零次評価と微分条件。 -/
lemma vertexInputLift_face (M : ModuleCat.{u} A) (v : Fin 2 → M) (b : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputLift A M v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) = v b :=
  (congrArg (fun x => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputLift A M v x) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector_vertex_eq A b)).trans
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputLift_vertex A M v b)

/-- 概要：辺線形延長を実際の面生成元で評価する（BF §3.1）。
方針：面表示の辺を正規化鎖表示へ移し、既存の評価を使う。
規約：標的は任意の係数加群。
使われ方：区間射の −1 次評価と微分条件。 -/
lemma edgeInputLift_face (M : ModuleCat.{u} A) (e : M) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputLift A M e (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) = e :=
  (congrArg (fun x => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputLift A M e x) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector_edge_eq A)).trans
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputLift_edge A M e)

/-- 概要：頂点二像・辺一像で指定する区間射の全整数成分（BM 命題 4.1）。
方針：零次と −1 次は生成元の線形延長、他次数は零射を使う。
規約：まだ像の微分条件を要求しない。
使われ方：区間射の微分保存を三生成元で検証する。 -/
def intervalMapComponent (K : Complex A) (v : Fin 2 → K.X 0) (e : K.X (-1))
    (r : ℤ) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X r ⟶ K.X r :=
  if hr : r = 0 then
    eqToHom (congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X t) hr) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputLift A (K.X 0) v ≫
      eqToHom (congrArg K.X hr.symm)
  else if hr1 : r = -1 then
    eqToHom (congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X t) hr1) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputLift A (K.X (-1)) e ≫
      eqToHom (congrArg K.X hr1.symm)
  else 0

/-- 概要：区間射の零次成分は両頂点の線形延長（BF §3.1）。
方針：次数等式の移送を消す。
規約：指定した頂点二像を使う。
使われ方：頂点での微分保存と射の評価。 -/
lemma intervalMapComponent_zero (K : Complex A) (v : Fin 2 → K.X 0) (e : K.X (-1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent A K v e 0 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputLift A (K.X 0) v := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent]

/-- 概要：区間射の −1 次成分は辺の線形延長（BF §3.1）。
方針：零次分岐を除き、次数移送を消す。
規約：指定した辺一像を使う。
使われ方：辺での微分保存と射の評価。 -/
lemma intervalMapComponent_negOne (K : Complex A) (v : Fin 2 → K.X 0) (e : K.X (-1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent A K v e (-1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputLift A (K.X (-1)) e := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent]

/-- 概要：区間射の他の成分は零（BF §3.1）。
方針：零次と −1 次の両分岐を除く。
規約：全整数次数。
使われ方：複体射の残余次数の微分条件。 -/
lemma intervalMapComponent_other (K : Complex A) (v : Fin 2 → K.X 0) (e : K.X (-1))
    (r : ℤ) (hr0 : r ≠ 0) (hr1 : r ≠ -1) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent A K v e r = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent, dite_eq_right hr0, dite_eq_right hr1]

/-- 概要：閉じた頂点像と両端差を境界に持つ辺像は全微分条件を満たす（BM 命題 4.1）。
方針：零次は両頂点、−1 次は一辺、他次数は始域の零性で比較する。
規約：任意の非有界標的複体。
使われ方：全整数成分を実際の区間射へ束ねる。 -/
lemma intervalMapComponent_comm (K : Complex A) (v : Fin 2 → K.X 0) (e : K.X (-1))
    (hv : ∀ b, K.d 0 1 (v b) = 0) (he : K.d (-1) 0 e = v 1 - v 0) (r : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent A K v e r ≫ K.d r (r + 1) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d r (r + 1) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent A K v e (r + 1) := by
  by_cases hr0 : r = 0
  · subst r
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent A K v e 0 ≫ K.d 0 1 =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d 0 1 ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent A K v e 1
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent_other A K v e 1 (by decide) (by decide),
      comp_zero]
    apply ModuleCat.hom_ext
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInput_linear_ext A
    intro b
    change K.d 0 1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputLift A (K.X 0) v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b))) = 0
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputLift_face]
    exact hv b
  · by_cases hr1 : r = -1
    · subst r
      change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent A K v e (-1) ≫ K.d (-1) 0 =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d (-1) 0 ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent A K v e 0
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent_negOne, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMapComponent_zero]
      apply ModuleCat.hom_ext
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInput_linear_ext A
      change K.d (-1) 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputLift A (K.X (-1)) e (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge)) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputLift A (K.X 0) v ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d (-1) 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge))
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputLift_face, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector_edge_d_sub, map_sub, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputLift_face,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputLift_face]
      exact he
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hx := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_eq_zero_of_other A r hr0 hr1 x
      simp only [hx, map_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
