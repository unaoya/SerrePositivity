module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.IntervalGeneratorExt
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComplexDegrees

/-!
模型。文献の定義との比較は後で
# 区間余演算の全整数次数のテンソル成分

概要：Berger–Fresse §2.2.6 の実際の頂点・辺の双線形余演算を全整数次数の成分族へ移す。
方針：χ の非正次数を語加群へ戻し、区間の零・−1 成分と出力次数を等式の射で移す。
規約：χ の正次数と他の区間次数では零写像。
使われ方：Leibniz 条件を証明して実際の余演算を tensorLift へ束ねる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：頂点次数分岐の全整数双線形余演算（BF §2.2.6）。
方針：χ の次数比較・区間入力の等式・出力次数の等式を順に適用する。
規約：入力の和の等式と非正性を証明で要求する。
使われ方：全整数成分族の零区間入力分岐。 -/
def cochainActionVertex (n : ℕ) (r s t : ℤ) (h : r + s = t) (hr : r ≤ 0) (hs : s = 0) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X r →ₗ[A] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X s →ₗ[A] (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X t :=
  ((((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputBilinear A n (-r).toNat).comp
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIsoNonpos A n r hr).hom.hom).compl₂
      (eqToHom (congrArg (fun q : ℤ => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X q) hs)).hom).compr₂
        (eqToHom (congrArg (fun q : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X q)
          (by omega : -(((-r).toNat : ℕ) : ℤ) = t))).hom)

/-- 概要：辺次数分岐の全整数双線形余演算（BF §2.2.6）。
方針：χ の次数比較・区間の −1 次数への等式・出力次数の等式を適用する。
規約：入力の和の等式と非正性を証明で要求する。
使われ方：全整数成分族の辺入力分岐。 -/
def cochainActionEdge (n : ℕ) (r s t : ℤ) (h : r + s = t) (hr : r ≤ 0) (hs : s = -1) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X r →ₗ[A] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X s →ₗ[A] (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X t :=
  ((((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputBilinear A n (-r).toNat).comp
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIsoNonpos A n r hr).hom.hom).compl₂
      (eqToHom (congrArg (fun q : ℤ => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X q) hs)).hom).compr₂
        (eqToHom (congrArg (fun q : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X q)
          (by omega : -((((-r).toNat + 1 : ℕ)) : ℤ) = t))).hom)

/-- 概要：区間余演算の全整数次数の双線形写像（BF §2.2.6）。
方針：χ の非正次数で零・−1 の区間入力を分け、それ以外を零とする。
規約：まだ微分条件を仮定せず、実際の値から成分を構成する。
使われ方：テンソル複体上の余演算の成分族。 -/
def cochainActionBilinear (n : ℕ) (r s t : ℤ) (h : r + s = t) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X r →ₗ[A] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X s →ₗ[A] (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X t :=
  if hr : r ≤ 0 then
    if hs : s = 0 then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionVertex A n r s t h hr hs
    else if he : s = -1 then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionEdge A n r s t h hr he else 0
  else 0

/-- 概要：全整数双線形成分の負語次数・頂点入力での値（BF §2.2.6）。
方針：非零分岐と全次数の移送を簡約する。
規約：χ の成分は実際の全射語加群へ戻す。
使われ方：頂点入力の微分条件を既存の線形恒等式へ戻す。 -/
lemma cochainActionBilinear_neg_vertex (n d : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X (-(d : ℤ))) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear A n (-(d : ℤ)) 0 (-(d : ℤ)) (by omega) x y =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputBilinear A n d ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).hom x) y := by
  cases d <;> rfl

/-- 概要：全整数双線形成分の負語次数・辺入力での値（BF §2.2.6）。
方針：非零分岐と全次数の移送を簡約する。
規約：出力次数は −(d+1)。
使われ方：辺入力の微分条件を既存の線形恒等式へ戻す。 -/
lemma cochainActionBilinear_neg_edge (n d : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X (-(d : ℤ))) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X (-1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear A n (-(d : ℤ)) (-1) (-((d + 1 : ℕ) : ℤ)) (by omega) x y =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputBilinear A n d ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).hom x) y := by
  cases d <;> rfl

/-- 概要：全整数の双線形余演算を加群テンソルの射へ移す（BF §2.2.6）。
方針：加群テンソルの普遍性を適用する。
規約：第一因子は χ、第二因子は実際の区間。
使われ方：tensorLift に渡す全整数次数の成分。 -/
def cochainActionComponent (n : ℕ) (r s t : ℤ) (h : r + s = t) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X r ⊗ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X s ⟶ (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X t :=
  ModuleCat.ofHom (TensorProduct.lift (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear A n r s t h))

/-- 概要：テンソル成分の純粋テンソル評価は実際の双線形余演算（BF §2.2.6）。
方針：テンソル普遍性の評価公式を使う。
規約：全整数次数と任意の和の証明。
使われ方：成分の Leibniz 条件を元で比較する。 -/
@[simp] lemma cochainActionComponent_tmul (n : ℕ) (r s t : ℤ) (h : r + s = t)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X r) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X s) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionComponent A n r s t h (x ⊗ₜ[A] y) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear A n r s t h x y := rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
