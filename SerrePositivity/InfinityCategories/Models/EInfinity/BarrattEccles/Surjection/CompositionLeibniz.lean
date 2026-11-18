module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransportCompatibility
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Surjectivity
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeibnizChains

/-!
模型。文献の定義との比較は後で
# 全射語の部分合成の Leibniz 則

概要：Berger–Fresse §1.2.3–5 の符号付き削除微分と部分合成の両立を証明する。
方針：全射 TR で二入力を BE 鎖へ持ち上げ、合成・微分・次数移送の保存を使う。
規約：任意の可換環、全 arity、零を含む両入力次数。Koszul 符号は整数作用。
使われ方：χ の部分合成を実際の複体の射にまとめる微分条件。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable (A : Type u) [CommRing A]

/-- 概要：両入力が正次数の全射語の部分合成は符号付き Leibniz 則を満たす（BF §1.2.3–5）。
方針：二入力を全射 TR で持ち上げ、BE の正次数の法則へ TR を適用する。
規約：第二項の符号は (−1)^(p+1)、第一項は等しい出力次数へ移送する。
使われ方：χ の二つの正次数成分の合成を鎖写像にする。 -/
lemma partialComposition_d_positive (m n : ℕ) (k : Fin (m + 1)) (p q : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + 1) (p + 1)) (y : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n (q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A (m + n) (p + 1 + q)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n (p + 1) (q + 1) k x y) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeTransport A (m + n) (by omega : p + (q + 1) = p + 1 + q)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n p (q + 1) k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A (m + 1) p x) y) +
      (-1 : ℤ) ^ (p + 1) •
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n (p + 1) q k x (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n q y) := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A (m + 1) (p + 1) x
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A n (q + 1) y
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + n) (p + 1 + q))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear_d_positive A m n k p q x y)
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_d A (m + n) (p + 1 + q)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear A m n k (p + 1) (q + 1) x y),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffleBilinear A k x y] at h
  simpa only [map_add, map_zsmul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_degreeTransport,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffleBilinear, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_d] using h

/-- 概要：外側次数零の部分合成は内側微分と可換（BF §1.2.3–5）。
方針：全射 TR で二入力を持ち上げ、BE の左次数零の法則を移す。
規約：内側の次数は q+1。nullary も含む。
使われ方：χ の次数零・正次数成分の鎖写像条件。 -/
lemma partialComposition_d_leftZero (m n : ℕ) (k : Fin (m + 1)) (q : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + 1) 0) (y : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n (q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A (m + n) (0 + q) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n 0 (q + 1) k x y) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n 0 q k x (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n q y) := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A (m + 1) 0 x
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A n (q + 1) y
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + n) (0 + q))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear_d_leftZero A m n k q x y)
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_d A (m + n) (0 + q)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear A m n k 0 (q + 1) x y),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffleBilinear A k x y] at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffleBilinear, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_d] using h

/-- 概要：内側次数零の部分合成は外側微分と可換（BF §1.2.3–5）。
方針：全射 TR で二入力を持ち上げ、BE の右次数零の法則を移す。
規約：外側の次数は p+1。空語の挿入も含む。
使われ方：χ の正次数・次数零成分の鎖写像条件。 -/
lemma partialComposition_d_rightZero (m n : ℕ) (k : Fin (m + 1)) (p : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + 1) (p + 1)) (y : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A (m + n) (p + 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n (p + 1) 0 k x y) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n p 0 k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A (m + 1) p x) y := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A (m + 1) (p + 1) x
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A n 0 y
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + n) (p + 0))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear_d_rightZero A m n k p x y)
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_d A (m + n) (p + 0)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear A m n k (p + 1) 0 x y),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffleBilinear A k x y] at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffleBilinear, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_d] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
