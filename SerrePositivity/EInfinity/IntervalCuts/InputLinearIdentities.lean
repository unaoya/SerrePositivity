module

public import SerrePositivity.EInfinity.IntervalCuts.CochainActionComponents

/-!
# 実際の区間入力上の双線形成分の線形微分等式

概要：Berger–Fresse §2.2.7 の語加群上の微分恒等式を、実際の区間成分上の写像へ移す。
方針：二頂点・一辺による外延性と指定入力での双線形成分評価を使う。
規約：全ての区間入力を扱い、生成元の条件を外部仮定としない。
使われ方：全整数の双線形余演算の Leibniz 則への移送。
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

/-- 概要：整数区間の標準辺生成元の微分は二頂点生成元の差（BF §2.2.7）。
方針：区間微分の負次数公式と次数比較同型を使う。
規約：入力次数 −1、出力次数零。
使われ方：零語次数の辺入力に対する Leibniz 則。 -/
lemma intervalInput_edge_d :
    (interval A).d (-1) 0 ((intervalXIso A 1).inv (edgeChain A)) =
      (intervalXIso A 0).inv (vertexChain A 1) - (intervalXIso A 0).inv (vertexChain A 0) := by
  change (interval A).d (-((1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ))
    ((intervalXIso A 1).inv (edgeChain A)) = _
  rw [interval_d_neg]
  change (intervalXIso A 0).inv ((intervalChains A).d 1 0
    ((intervalXIso A 1).toLinearEquiv
      ((intervalXIso A 1).toLinearEquiv.symm (edgeChain A)))) = _
  rw [LinearEquiv.apply_symm_apply, edgeChain_d, map_sub]

/-- 概要：実際の区間零入力に対する頂点余演算の出力微分は零（BF §2.2.7）。
方針：二頂点で比較して語加群全体の頂点微分恒等式へ戻す。
規約：第一入力は任意の全射語加群の元。
使われ方：頂点入力分岐の標的微分項。 -/
lemma vertexInputBilinear_d_eq_zero (n d : ℕ) (x : degreeModule A n d) :
    ((power (interval A) n).d (-(d : ℤ)) (-(d : ℤ) + 1)).hom.comp
      (vertexInputBilinear A n d x) = 0 := by
  have h : ModuleCat.ofHom (((power (interval A) n).d (-(d : ℤ))
        (-(d : ℤ) + 1)).hom.comp (vertexInputBilinear A n d x)) =
      (0 : (interval A).X 0 ⟶ (power (interval A) n).X (-(d : ℤ) + 1)) := by
    apply vertexInput_hom_ext A
    intro b
    change (power (interval A) n).d (-(d : ℤ)) (-(d : ℤ) + 1)
      (vertexInputBilinear A n d x ((intervalXIso A 0).inv (vertexChain A b))) = 0
    rw [vertexInputBilinear_vertex]
    exact congrArg (fun f : degreeModule A n d →ₗ[A]
      (power (interval A) n).X (-(d : ℤ) + 1) => f x) (vertexComponent_d_eq_zero A n d b)
  exact congrArg (fun f => f.hom) h

/-- 概要：削除微分の任意の元に対する実際の区間零入力の余演算は零（BF §2.2.7）。
方針：二頂点の評価で頂点成分と削除微分の線形等式へ戻す。
規約：語次数 d+1 から d の全次数。
使われ方：頂点入力分岐の第一因子微分項。 -/
lemma vertexInputBilinear_differential (n d : ℕ) (x : degreeModule A n (d + 1)) :
    vertexInputBilinear A n d (differential A n d x) = 0 := by
  have h : ModuleCat.ofHom (vertexInputBilinear A n d (differential A n d x)) =
      (0 : (interval A).X 0 ⟶ (power (interval A) n).X (-(d : ℤ))) := by
    apply vertexInput_hom_ext A
    intro b
    change vertexInputBilinear A n d (differential A n d x)
      ((intervalXIso A 0).inv (vertexChain A b)) = 0
    rw [vertexInputBilinear_vertex]
    exact congrArg (fun f : degreeModule A n (d + 1) →ₗ[A]
      (power (interval A) n).X (-(d : ℤ)) => f x) (vertexComponent_differential A n d b)
  exact congrArg (fun f => f.hom) h

/-- 概要：正次数の実際の辺入力余演算は語の削除微分と可換（BF §2.2.7）。
方針：一辺で比較して語加群全体の辺微分恒等式を使う。
規約：語次数 d+1 から d、区間入力次数 −1。
使われ方：正語次数の辺入力分岐の Leibniz 則。 -/
lemma edgeInputBilinear_d_positive (n d : ℕ) (x : degreeModule A n (d + 1)) :
    ((power (interval A) n).d (-((d + 2 : ℕ) : ℤ)) (-((d + 1 : ℕ) : ℤ))).hom.comp
        (edgeInputBilinear A n (d + 1) x) =
      edgeInputBilinear A n d (differential A n d x) := by
  have h : ModuleCat.ofHom (((power (interval A) n).d (-((d + 2 : ℕ) : ℤ))
      (-((d + 1 : ℕ) : ℤ))).hom.comp (edgeInputBilinear A n (d + 1) x)) =
      ModuleCat.ofHom (edgeInputBilinear A n d (differential A n d x)) := by
    apply edgeInput_hom_ext A
    change (power (interval A) n).d (-((d + 2 : ℕ) : ℤ)) (-((d + 1 : ℕ) : ℤ))
      (edgeInputBilinear A n (d + 1) x ((intervalXIso A 1).inv (edgeChain A))) =
        edgeInputBilinear A n d (differential A n d x)
          ((intervalXIso A 1).inv (edgeChain A))
    rw [edgeInputBilinear_edge, edgeInputBilinear_edge]
    exact congrArg (fun f : degreeModule A n (d + 1) →ₗ[A]
      (power (interval A) n).X (-((d + 1 : ℕ) : ℤ)) => f x) (edgeComponent_d_positive A n d)
  exact congrArg (fun f => f.hom) h

/-- 概要：零語次数の実際の辺入力余演算は入力区間の微分と可換（BF §2.2.7）。
方針：一辺で比較し、区間の二端点差と零次数の辺成分の恒等式を使う。
規約：語次数零では χ の標的正次数は零。
使われ方：零語次数の辺入力分岐の Leibniz 則。 -/
lemma edgeInputBilinear_d_zero (n : ℕ) (x : degreeModule A n 0) :
    ((power (interval A) n).d (-1) 0).hom.comp (edgeInputBilinear A n 0 x) =
      (vertexInputBilinear A n 0 x).comp ((interval A).d (-1) 0).hom := by
  have h : ModuleCat.ofHom (((power (interval A) n).d (-1) 0).hom.comp
      (edgeInputBilinear A n 0 x)) = ModuleCat.ofHom
        ((vertexInputBilinear A n 0 x).comp ((interval A).d (-1) 0).hom) := by
    apply edgeInput_hom_ext A
    change (power (interval A) n).d (-1) 0
        (edgeInputBilinear A n 0 x ((intervalXIso A 1).inv (edgeChain A))) =
      vertexInputBilinear A n 0 x ((interval A).d (-1) 0
        ((intervalXIso A 1).inv (edgeChain A)))
    rw [edgeInputBilinear_edge, intervalInput_edge_d, map_sub,
      vertexInputBilinear_vertex, vertexInputBilinear_vertex]
    exact congrArg (fun f : degreeModule A n 0 →ₗ[A] (power (interval A) n).X 0 => f x)
      (edgeComponent_d_zero A n)
  exact congrArg (fun f => f.hom) h

/-- 概要：正語次数では実際の任意の頂点入力の余演算は零（BF §2.2.6）。
方針：二頂点の外延性で既存の頂点成分の零性へ帰着する。
規約：任意の係数環と全 arity。
使われ方：辺入力の Leibniz 則の第二項を消去する。 -/
lemma vertexInputBilinear_eq_zero_of_positive (n d : ℕ) (hd : 0 < d)
    (x : degreeModule A n d) : vertexInputBilinear A n d x = 0 := by
  have h : ModuleCat.ofHom (vertexInputBilinear A n d x) =
      (0 : (interval A).X 0 ⟶ (power (interval A) n).X (-(d : ℤ))) := by
    apply vertexInput_hom_ext A
    intro b
    change vertexInputBilinear A n d x
      ((intervalXIso A 0).inv (vertexChain A b)) = 0
    rw [vertexInputBilinear_vertex, vertexComponent_eq_zero_of_positive A n d b hd]
    rfl
  exact congrArg (fun f => f.hom) h

end SerrePositivity.EInfinity.IntervalCuts
