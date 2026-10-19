module

public import SerrePositivity.EInfinity.IntervalCuts.IntervalLinearLifts
public import SerrePositivity.EInfinity.IntervalCuts.ComponentLinearIdentities

/-!
# 実際の区間入力の頂点・辺の双線形成分

概要：Berger–Fresse §2.2.6 の計算済み切断値を χ の語加群と実際の区間成分の双線形写像へまとめる。
方針：区間の線形延長の値域を線形写像の加群に取り、二入力を反転する。
規約：区間入力次数は零と −1、出力次数はそれぞれ −d と −(d+1)。
使われ方：全整数次数のテンソル成分から余演算の複体射を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：二頂点で指定した値を整数表示の区間零成分へ線形延長する（BF §2.2.6）。
方針：自然数鎖成分への比較同型に零次の線形延長を続ける。
規約：実際の正規化区間を使う。
使われ方：余演算の頂点入力の成分。 -/
def vertexInputLift (M : ModuleCat.{u} A) (v : Fin 2 → M) : (interval A).X 0 ⟶ M :=
  (intervalXIso A 0).hom ≫ vertexChainLift A M v

/-- 概要：一辺で指定した値を整数表示の区間一次成分へ線形延長する（BF §2.2.6）。
方針：自然数鎖成分への比較同型に一次の線形延長を続ける。
規約：入力整数次数は −1。
使われ方：余演算の辺入力の成分。 -/
def edgeInputLift (M : ModuleCat.{u} A) (e : M) : (interval A).X (-1) ⟶ M :=
  (intervalXIso A 1).hom ≫ edgeChainLift A M e

/-- 概要：整数区間の端点生成元は指定した頂点値へ移る（BF §2.2.6）。
方針：次数比較の逆・順を消し、自然数鎖の評価を使う。
規約：零・一の両端点。
使われ方：双線形余演算の頂点での基底値。 -/
@[simp] lemma vertexInputLift_vertex (M : ModuleCat.{u} A) (v : Fin 2 → M) (b : Fin 2) :
    vertexInputLift A M v ((intervalXIso A 0).inv (vertexChain A b)) = v b := by
  change vertexChainLift A M v ((intervalXIso A 0).toLinearEquiv
    ((intervalXIso A 0).toLinearEquiv.symm (vertexChain A b))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact vertexChainLift_vertex A M v b

/-- 概要：整数区間の辺生成元は指定した辺値へ移る（BF §2.2.6）。
方針：次数比較の逆・順を消し、自然数鎖の評価を使う。
規約：向きは零から一。
使われ方：双線形余演算の辺での基底値。 -/
@[simp] lemma edgeInputLift_edge (M : ModuleCat.{u} A) (e : M) :
    edgeInputLift A M e ((intervalXIso A 1).inv (edgeChain A)) = e := by
  change edgeChainLift A M e ((intervalXIso A 1).toLinearEquiv
    ((intervalXIso A 1).toLinearEquiv.symm (edgeChain A))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact edgeChainLift_edge A M e

/-- 概要：全射語と実際の区間零成分の双線形余演算（BF §2.2.6）。
方針：頂点成分の線形写像を値とする区間線形延長を作って入力を反転する。
規約：第一入力は語次数 d、第二入力は整数次数零。
使われ方：全整数余演算の非零な頂点入力分岐。 -/
def vertexInputBilinear (n d : ℕ) : degreeModule A n d →ₗ[A] (interval A).X 0 →ₗ[A]
    (power (interval A) n).X (-(d : ℤ)) :=
  (vertexInputLift A (ModuleCat.of A
    (degreeModule A n d →ₗ[A] (power (interval A) n).X (-(d : ℤ))))
      (fun b => vertexComponent A n d b)).hom.flip

/-- 概要：全射語と実際の区間一次成分の双線形余演算（BF §2.2.6）。
方針：辺成分の線形写像を値とする区間線形延長を作って入力を反転する。
規約：第一入力は語次数 d、第二入力は整数次数 −1。
使われ方：全整数余演算の非零な辺入力分岐。 -/
def edgeInputBilinear (n d : ℕ) : degreeModule A n d →ₗ[A] (interval A).X (-1) →ₗ[A]
    (power (interval A) n).X (-((d + 1 : ℕ) : ℤ)) :=
  (edgeInputLift A (ModuleCat.of A
    (degreeModule A n d →ₗ[A] (power (interval A) n).X (-((d + 1 : ℕ) : ℤ))))
      (edgeComponent A n d)).hom.flip

/-- 概要：双線形な頂点入力成分は計算済みの実際の頂点成分を返す（BF §2.2.6）。
方針：区間線形延長の生成元評価を線形写像に適用する。
規約：第一入力は全射語加群の任意の元。
使われ方：双線形成分の微分条件と作用の基底評価。 -/
lemma vertexInputBilinear_vertex (n d : ℕ) (x : degreeModule A n d) (b : Fin 2) :
    vertexInputBilinear A n d x ((intervalXIso A 0).inv (vertexChain A b)) =
      vertexComponent A n d b x := by
  exact congrArg (fun f : degreeModule A n d →ₗ[A]
      (power (interval A) n).X (-(d : ℤ)) => f x)
    (vertexInputLift_vertex A (ModuleCat.of A
      (degreeModule A n d →ₗ[A] (power (interval A) n).X (-(d : ℤ))))
        (fun b => vertexComponent A n d b) b)

/-- 概要：双線形な辺入力成分は計算済みの実際の辺成分を返す（BF §2.2.6）。
方針：区間線形延長の生成元評価を線形写像に適用する。
規約：第一入力は全射語加群の任意の元。
使われ方：双線形成分の微分条件と作用の基底評価。 -/
lemma edgeInputBilinear_edge (n d : ℕ) (x : degreeModule A n d) :
    edgeInputBilinear A n d x ((intervalXIso A 1).inv (edgeChain A)) =
      edgeComponent A n d x := by
  exact congrArg (fun f : degreeModule A n d →ₗ[A]
      (power (interval A) n).X (-((d + 1 : ℕ) : ℤ)) => f x)
    (edgeInputLift_edge A (ModuleCat.of A
      (degreeModule A n d →ₗ[A] (power (interval A) n).X (-((d + 1 : ℕ) : ℤ))))
        (edgeComponent A n d))

end SerrePositivity.EInfinity.IntervalCuts
