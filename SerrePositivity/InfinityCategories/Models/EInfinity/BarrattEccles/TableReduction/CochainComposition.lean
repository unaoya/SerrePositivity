module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CochainDegrees
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransportCompatibility
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CochainComposition
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCochainDifferential

/-!
模型。文献の定義との比較は後で
# 整数 TR の双線形部分合成保存

概要：Berger–Fresse §1.3・§1.5 の全鎖次数の合成保存を全整数コチェイン次数へ移す。
方針：非正次数では比較同型と正規化 TR の保存、正次数では入力元の零性を使う。
規約：出力次数は和に等しい任意の整数次数で指定する。
使われ方：χ の複体射の部分合成と TR オペラッド射を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：全整数次数で TR は実際の双線形合成成分を保存する（BF §1.3・§1.5）。
方針：正次数の入力を零とし、非正次数を比較同型を通じて全鎖次数の保存へ移す。
規約：nullary と出力 arity 零を含む。
使われ方：整数 Leibniz 則と複体射の合成保存の主経路。 -/
lemma cochainMap_compositionBilinear (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t)
    (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A (m + 1)).X r) (y : (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n).X s) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n)).f t (_root_.SerrePositivity.EInfinity.BarrattEccles.cochainShuffleBilinear A m n i r s t h x y) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear A m n i r s t h
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1)).f r x) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n).f s y) := by
  by_cases hr : r ≤ 0
  · by_cases hs : s ≤ 0
    · rw [_root_.SerrePositivity.EInfinity.BarrattEccles.cochainShuffleBilinear_of_nonpos A m n i r s t h hr hs,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear_of_nonpos A m n i r s t h hr hs]
      dsimp only [_root_.SerrePositivity.EInfinity.BarrattEccles.cochainShuffleBilinearNonpos,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionNonpos, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
        LinearMap.comp_apply]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_nonpos_inv_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_degreeTransport,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffleBilinear, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_nonpos_hom_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_nonpos_hom_apply]
    · have hy := _root_.SerrePositivity.EInfinity.BarrattEccles.complex_eq_zero_of_positive A n s (by omega) y
      simp only [hy, map_zero]
  · have hx := _root_.SerrePositivity.EInfinity.BarrattEccles.complex_eq_zero_of_positive A (m + 1) r (by omega) x
    simp only [hx, map_zero, LinearMap.zero_apply]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
