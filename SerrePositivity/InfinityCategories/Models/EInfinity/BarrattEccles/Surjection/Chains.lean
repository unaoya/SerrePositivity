module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DifferentialSquare

/-!
模型。文献の定義との比較は後で
# 全射語の実際の鎖複体

概要：Berger–Fresse §1.2.3・§1.4.4 の全射語と符号付き削除から χ の複体を構成する。
方針：TR から導いた平方零を既存の非負鎖複体の構成へ渡す。
規約：任意の可換環、全 arity、ホモロジー次数。
使われ方：一般の table reduction 鎖写像と χ のオペラッド構造の構成へ進む。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.CategoryTheory

/-- 概要：全射語の符号付き削除による非負鎖複体（BF §1.2.3・§1.4.4）。
方針：各次数の自由加群と線形削除を束ね、TR 由来の平方零を適用する。
規約：次数 d の基底は長さ n+d の非退化全射語。
使われ方：χ の arity ごとの複体。 -/
def normalizedChains (A : Type u) [CommRing A] (n : ℕ) : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun d => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d) (fun d => ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d))
    (fun d => by
      apply ModuleCat.hom_ext
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.differential_comp_differential A n d)

/-- 概要：χ の複体の隣接微分は元の符号付き削除（BF §1.2.3）。
方針：ChainComplex.of の隣接微分を評価する。
規約：複体の射としての等式。
使われ方：TR の微分保存を鎖写像の可換性へ移す。 -/
@[simp] lemma normalizedChains_d (A : Type u) [CommRing A] (n d : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedChains A n).d (d + 1) d = ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d) := by
  apply ChainComplex.of_d

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
