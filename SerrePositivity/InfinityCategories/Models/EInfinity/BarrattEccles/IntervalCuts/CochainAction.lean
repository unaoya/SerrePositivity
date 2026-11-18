module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CochainLeibniz
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
模型。文献の定義との比較は後で
# 区間切断余演算の整数複体射

概要：Berger–Fresse §2.2.6–7 の区間切断を χ(n) ⊗ N_*(Δ¹) からの複体射へまとめる。
方針：全整数の双線形 Leibniz 則を純粋テンソルで評価し、tensorLift を適用する。
規約：非有界整数コチェインと既存の Koszul テンソルを使う。
使われ方：区間の χ-coalgebra の演算の供給。余代数法則は別途証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：区間余演算のテンソル成分は微分と両立（BF §2.2.7）。
方針：純粋テンソルの外延性で双線形 Leibniz 則へ帰着する。
規約：第二微分項の符号は第一の整数入力次数。
使われ方：tensorLift の微分条件。 -/
lemma cochainActionComponent_d (n : ℕ) (r s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionComponent A n r s (r + s) rfl ≫
        (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (r + s) (r + s + 1) =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).d r (r + 1) ▷ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X s) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionComponent A n (r + 1) s (r + s + 1) (by omega) +
      r.negOnePow • (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X r ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d s (s + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionComponent A n r (s + 1) (r + s + 1) (by omega)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear_d A n r s x y

/-- 概要：区間切断余演算の実際の整数複体射（BF §2.2.6–7）。
方針：全整数成分族と微分条件を tensorLift へ渡す。
規約：第一因子は χ(n)、第二因子は正規化区間、出力は区間の n 重テンソル。
使われ方：χ-coalgebra 構造の演算と TR に沿う E への制限。 -/
def cochainAction (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A ⟶ power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n :=
  tensorLift (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionComponent A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionComponent_d A n)

/-- 概要：区間余演算の複体射の斉次成分は指定したテンソル成分（BF §2.2.6）。
方針：全テンソルの直和の普遍性を評価する。
規約：全整数入力次数と和の任意の等式。
使われ方：余代数法則を斉次成分で比較する。 -/
@[reassoc (attr := simp)] lemma ι_cochainAction (n : ℕ) (r s t : ℤ) (h : r + s = t) :
    ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) r s t h ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n).f t = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionComponent A n r s t h :=
  ι_tensorLift _ _ r s t h

/-- 概要：負語次数の頂点入力で複体射は実際の頂点双線形演算（BF §2.2.6）。
方針：斉次成分の式と双線形成分の負次数評価を使う。
規約：頂点入力は実際の区間の任意の零次数元。
使われ方：二端点と余演算の整合性。 -/
lemma cochainAction_neg_vertex (n d : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X (-(d : ℤ))) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X 0) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n).f (-(d : ℤ))
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (-(d : ℤ)) 0 (-(d : ℤ))
        (by omega) (x ⊗ₜ[A] y)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputBilinear A n d ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).hom x) y := by
  have h := congrArg (fun f => f (x ⊗ₜ[A] y))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ι_cochainAction A n (-(d : ℤ)) 0 (-(d : ℤ)) (by omega))
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear_neg_vertex A n d x y)

/-- 概要：負語次数の辺入力で複体射は実際の辺双線形演算（BF §2.2.6）。
方針：斉次成分の式と双線形成分の負次数評価を使う。
規約：出力次数は −(d+1)。
使われ方：有限区間切断の値と複体射の照合。 -/
lemma cochainAction_neg_edge (n d : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X (-(d : ℤ))) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X (-1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n).f (-((d + 1 : ℕ) : ℤ))
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (-(d : ℤ)) (-1)
        (-((d + 1 : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputBilinear A n d ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).hom x) y := by
  have h := congrArg (fun f => f (x ⊗ₜ[A] y))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ι_cochainAction A n (-(d : ℤ)) (-1) (-((d + 1 : ℕ) : ℤ)) (by omega))
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear_neg_edge A n d x y)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
