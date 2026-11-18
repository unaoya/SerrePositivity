module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ZeroTensorPowers
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CochainAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ZeroAugmentation

/-!
模型。文献の定義との比較は後で
# 零次の頂点余作用と端点・収縮の反復テンソル値

概要：Berger–Fresse §2.2.6・§3.1 の零次余作用を係数和と一定頂点テンソルで表す。
方針：χ の語基底から線形延長し、零次純粋テンソルの自然性を使う。
規約：nullary を含む全 arity、任意の可換環。
使われ方：E-coalgebra 区間の端点・収縮の零次保存条件。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：零次の任意の χ 係数の頂点値は係数和倍の一定頂点テンソル（BF §3.1）。
方針：両線形写像を全ての語基底で比較する。
規約：全 arity と両頂点。
使われ方：一般の係数入力の余作用保存を TR の係数比較へ帰着する。 -/
lemma vertexComponent_zero_coefficient (n : ℕ) (b : Fin 2) (x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n 0 b x =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A n x • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) n := by
  have H : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n 0 b =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A n).smulRight
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) n) := by
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0).ext
    intro v
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_basis]
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord A v.down b =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0 (ULift.up v.down)) •
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (show (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X 0 from _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) n
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation_basis, one_smul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor_vertex]
    rfl
  exact congrArg (fun f => f x) H

/-- 概要：実際の零次余作用は係数和倍の一定頂点テンソル（BF §2.2.6・§3.1）。
方針：整数余作用の頂点評価を線形成分へ戻して係数和の公式を使う。
規約：任意の整数零次の χ 係数入力。
使われ方：端点・収縮の複体射としての保存則の零次計算。 -/
lemma cochainAction_zero_vertex (n : ℕ) (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X 0) (b : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n).f 0 (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) 0 0 0 rfl
      (x ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b))) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A n ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n 0).hom x) •
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) n := by
  refine (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_neg_vertex A n 0 x (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b))).trans ?_
  refine (congrArg (fun y => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputBilinear A n 0 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n 0).hom x) y)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector_vertex_eq A b)).trans ?_
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputBilinear_vertex A n 0 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n 0).hom x) b).trans
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_zero_coefficient A n b _)

/-- 概要：端点の反復テンソルは単位冪の一を一定頂点へ送る（BF §3.1）。
方針：単位の零次純粋テンソル表示と射の自然性を使う。
規約：両端点・零重テンソルを含む。
使われ方：単位余作用の後の端点の反復テンソルを評価する。 -/
lemma endpoint_power_unit (b : Bool) (n : ℕ) :
    (_root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b) n).f 0
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).inv.f 0
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex (if b then 1 else 0))) n := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor_unit A n, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.map_zeroTensor, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_zero_apply, one_smul]

/-- 概要：一定頂点出力の収縮の反復テンソル値は単位冪の一（BF §3.1）。
方針：反復テンソルの自然性と各頂点の収縮値を使う。
規約：全 arity・両頂点。
使われ方：収縮の余作用保存の零次出力を評価する。 -/
lemma contraction_power_vertex (b : Fin 2) (n : ℕ) :
    (_root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A) n).f 0
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) n) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).inv.f 0
          ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.map_zeroTensor, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction_vertex_eq, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor_unit]

/-- 概要：単位の反復テンソルは零以外の整数次数で零対象（BF §3.1）。
方針：標準の単位冪同型を各次数で評価して single 複体の零性を移す。
規約：全 arity・全整数次数。
使われ方：収縮の余作用保存の零次以外の出力条件を消去する。 -/
lemma unitPower_isZero_of_ne_zero (n : ℕ) (r : ℤ) (hr : r ≠ 0) :
    IsZero ((power (𝟙_ (Complex A)) n).X r) :=
  IsZero.of_iso (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) r hr)
    ((eval (ModuleCat A) (.up ℤ) r).mapIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
