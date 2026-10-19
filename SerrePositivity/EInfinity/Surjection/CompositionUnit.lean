module

public import SerrePositivity.EInfinity.TableReduction.TransportCompatibility
public import SerrePositivity.EInfinity.TableReduction.Surjectivity
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleRightUnit
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeftUnit

/-!
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

namespace SerrePositivity.EInfinity.Surjection

open TableReduction

variable (A : Type u) [CommRing A]

/-- 概要：χ の単位は次数零・arity 一の唯一の基底語（BF §1.2.4）。
方針：恒等置換の一行表示を基底元にする。
規約：語は一文字の零。
使われ方：部分合成の左右の単位則と単位射を構成する。 -/
def unitElement : degreeModule A 1 0 :=
  basis A 1 0 (ULift.up (permutationWord (1 : Equiv.Perm (Fin 1))))

/-- 概要：正規化 TR は BE の単位を χ の一文字単位へ送る（BF §1.3）。
方針：次数零の TR を唯一の逆置換行で計算する。
規約：追加の単位保存を仮定しない。
使われ方：BE の左右の単位則を全射 TR から移す。 -/
lemma normalizedMap_unit :
    normalizedMap A 1 0 (BarrattEccles.normalizedGenerator A 1 0 BarrattEccles.unitSimplex) =
      unitElement A := by
  rw [normalizedMap_generator, onSequence_degree_zero A (by decide)]
  simp only [BarrattEccles.simplexEquiv_unitSimplex, inv_one, Equiv.Perm.one_apply]
  exact generator_word A (permutationWord 1)

/-- 概要：一文字単位への代入は arity・次数の移送後に元へ戻る（BF §1.2.4）。
方針：入力を全射 TR の逆像へ取り、BE の左単位則と単位保存を使う。
規約：入力 arity と次数は零を含む。
使われ方：χ の左単位則の成分公式。 -/
lemma partialComposition_left_unit (n q : ℕ) (y : degreeModule A n q) :
    degreeTransport A n (Nat.zero_add q)
        (arityTransport A (Nat.zero_add n) (0 + q)
          (partialComposition A 0 n 0 q 0 (unitElement A) y)) = y := by
  obtain ⟨y, rfl⟩ := normalizedMap_surjective A n q y
  have h := congrArg (normalizedMap A n q) (BarrattEccles.shuffleBilinear_left_unit A n q y)
  simp only [normalizedMap_degreeTransport, normalizedMap_arityTransport,
    normalizedMap_shuffleBilinear] at h
  erw [normalizedMap_unit A] at h
  exact h

/-- 概要：右から一文字単位を代入すると元へ戻る（BF §1.2.4）。
方針：入力を全射 TR の逆像へ取り、BE の右単位則を移す。
規約：任意の挿入位置と全次数。
使われ方：χ の右単位則の成分公式。 -/
lemma partialComposition_right_unit (m : ℕ) (i : Fin (m + 1)) (p : ℕ)
    (x : degreeModule A (m + 1) p) : partialComposition A m 1 p 0 i x (unitElement A) = x := by
  obtain ⟨x, rfl⟩ := normalizedMap_surjective A (m + 1) p x
  have h := normalizedMap_shuffleBilinear A (m := m) (n := 1) (d := p) (e := 0) i x
    (BarrattEccles.normalizedGenerator A 1 0 BarrattEccles.unitSimplex)
  rw [BarrattEccles.shuffleBilinear_right_unit, normalizedMap_unit] at h
  exact h.symm

end SerrePositivity.EInfinity.Surjection
