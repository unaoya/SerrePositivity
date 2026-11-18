module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransportCompatibility
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Surjectivity
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleRightUnit
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeftUnit

/-!
模型。文献の定義との比較は後で
# 全射語の単位と部分合成の単位則

概要：Berger–Fresse §1.2.4 の単位を次数零の一文字語として構成する。
方針：BE の単位生成元の TR を計算し、全射性で左右の単位則を移す。
規約：arity 0 の対象への左単位も含む。
使われ方：χ の dg オペラッドの単位と部分合成の成分法則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable (A : Type u) [CommRing A]

/-- 概要：χ の単位は次数零・arity 一の唯一の基底語（BF §1.2.4）。
方針：恒等置換の一行表示を基底元にする。
規約：語は一文字の零。
使われ方：部分合成の左右の単位則と単位射を構成する。 -/
def unitElement : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A 1 0 :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A 1 0 (ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 1))))

/-- 概要：正規化 TR は BE の単位を χ の一文字単位へ送る（BF §1.3）。
方針：次数零の TR を唯一の逆置換行で計算する。
規約：追加の単位保存を仮定しない。
使われ方：BE の左右の単位則を全射 TR から移す。 -/
lemma normalizedMap_unit :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A 1 0 (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A 1 0 _root_.SerrePositivity.EInfinity.BarrattEccles.unitSimplex) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.unitElement A := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_generator, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_degree_zero A (by decide)]
  simp only [_root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv_unitSimplex, inv_one, Equiv.Perm.one_apply]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord 1)

/-- 概要：一文字単位への代入は arity・次数の移送後に元へ戻る（BF §1.2.4）。
方針：入力を全射 TR の逆像へ取り、BE の左単位則と単位保存を使う。
規約：入力 arity と次数は零を含む。
使われ方：χ の左単位則の成分公式。 -/
lemma partialComposition_left_unit (n q : ℕ) (y : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeTransport A n (Nat.zero_add q)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.arityTransport A (Nat.zero_add n) (0 + q)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A 0 n 0 q 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.unitElement A) y)) = y := by
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A n q y
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n q) (_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear_left_unit A n q y)
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_degreeTransport, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_arityTransport,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffleBilinear] at h
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedMap_unit A] at h
  exact h

/-- 概要：右から一文字単位を代入すると元へ戻る（BF §1.2.4）。
方針：入力を全射 TR の逆像へ取り、BE の右単位則を移す。
規約：任意の挿入位置と全次数。
使われ方：χ の右単位則の成分公式。 -/
lemma partialComposition_right_unit (m : ℕ) (i : Fin (m + 1)) (p : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + 1) p) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m 1 p 0 i x (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.unitElement A) = x := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A (m + 1) p x
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffleBilinear A (m := m) (n := 1) (d := p) (e := 0) i x
    (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A 1 0 _root_.SerrePositivity.EInfinity.BarrattEccles.unitSimplex)
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear_right_unit, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedMap_unit] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
