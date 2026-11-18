module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RemainderCancellation

/-!
模型。文献の定義との比較は後で
# 一般の table reduction の微分保存

概要：Berger–Fresse §1.4.4 の一般の TR の微分保存を証明する。
方針：残余和の全単射による相殺を頂点境界の式へ代入し、正規化生成元から線形化する。
規約：任意の可換環、零 arity を含む全 arity・全次数。
使われ方：χ の平方零と複体構造、実際の TR 鎖写像の構成へ進む。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：全置換列で TR の微分は頂点境界に等しい（BF §1.4.4）。
方針：正の arity は全残余和の相殺、零 arity は空語の境界計算を使う。
規約：退化した頂点列と抽出出力も含む。
使われ方：正規化された E の全生成元で微分保存を検査する。 -/
lemma differential_onSequence_eq_vertexBoundary (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary A w := by
  cases n with
  | zero => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.differential_onSequence_nullary A d w
  | succ n =>
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary_identity_iff_remainder_zero A (by omega) w).mpr
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_remainderTerm_zero A w)

/-- 概要：一般の正規化 TR は線形微分を保つ（BF §1.4.4）。
方針：全生成元の境界恒等式を線形写像の判定へ渡す。
規約：保存則や残余の零性を仮定しない。
使われ方：TR の全射性から χ の平方零を移し、鎖写像を構成する。 -/
lemma normalizedMap_comm (A : Type u) [CommRing A] (n d : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n (d + 1)) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d).comp ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).d (d + 1) d).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_comm_of_vertexBoundary A n d
  intro w
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.differential_onSequence_eq_vertexBoundary A w

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
