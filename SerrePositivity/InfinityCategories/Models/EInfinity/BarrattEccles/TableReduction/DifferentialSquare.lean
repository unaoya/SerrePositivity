module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DifferentialPreservation
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Surjectivity

/-!
模型。文献の定義との比較は後で
# 全射語の微分の平方零

概要：Berger–Fresse §1.4.4 の全射性と微分保存から χ の平方零を導く。
方針：任意の全射語鎖を TR の原像へ持ち上げ、E の平方零を二回の微分保存で移す。
規約：全可換環、全 arity、全非負次数。
使われ方：χ の鎖複体と実際の table reduction 鎖写像を構成する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：全射語の符号付き削除微分は平方零（BF §1.4.4）。
方針：TR の全射性で原像を取り、一般の微分保存と E の平方零を使う。
規約：正規化 TR の次数ごとの線形切断が鎖写像であるとは要求しない。
使われ方：χ の複体の公理を追加仮定なしで供給する。 -/
lemma differential_comp_differential (A : Type u) [CommRing A] (n d : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n (d + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A n (d + 2) x
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n (d + 2) y)) = 0
  have hfirst := LinearMap.congr_fun (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_comm A n (d + 1)) y
  have hsecond := LinearMap.congr_fun (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_comm A n d)
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).d (d + 2) (d + 1)) y)
  simp only [LinearMap.comp_apply] at hfirst hsecond
  rw [hfirst, hsecond]
  have hz := congrArg
    (fun f : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).X (d + 2) ⟶
      (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).X d => f y)
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).d_comp_d (d + 2) (d + 1) d)
  change ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).d (d + 1) d)
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).d (d + 2) (d + 1)) y) = 0 at hz
  rw [hz, map_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
