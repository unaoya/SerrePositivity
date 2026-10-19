module

public import SerrePositivity.EInfinity.Surjection.ComplexAction
public import SerrePositivity.Spectra.SymmetricSequence.Basic

/-!
# 全射語複体の対称列

概要：Berger–Fresse §1.2 の χ を有限全単射の骨格上の整数複体の対称列へまとめる。
方針：有限全単射の置換を複体上の値の左置換へ送る。
規約：共変な左作用。Operad.rightAction は逆元から得る。
使われ方：χ の dg オペラッドの sequence 成分と TR の自然変換。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Surjection

open CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：骨格の有限全単射に沿う χ の構造射（BF §1.2.1）。
方針：同じ有限濃度の両端を同定し、対応する置換の左作用を使う。
規約：置換の逆元は取らず、値の左作用として扱う。
使われ方：対称列の map 成分。 -/
def sequenceMap {X Y : FiniteBijection} (f : X ⟶ Y) :
    complex A (FiniteBijection.card X) ⟶ complex A (FiniteBijection.card Y) := by
  obtain rfl := FiniteBijection.object_eq_of_hom f
  exact complexRename A (FiniteBijection.card X) (FiniteBijection.equivOfHom f)

/-- 概要：骨格の自己全単射の構造射は値の置換（BF §1.2.1）。
方針：両端の同定を恒等の場合に評価する。
規約：任意の骨格対象。
使われ方：対称列の関手法則と置換作用を比較する。 -/
@[simp] lemma sequenceMap_self {X : FiniteBijection} (f : X ⟶ X) :
    sequenceMap A f = complexRename A (FiniteBijection.card X) (FiniteBijection.equivOfHom f) := by
  simp [sequenceMap]

/-- 概要：χ の整数コチェイン複体の対称列（BF §1.2）。
方針：値の複体上の左作用を有限全単射の関手としてまとめる。
規約：arity 零を含む。
使われ方：χ の dg オペラッドの台の対称列。 -/
def sequence : SymmetricSequence (DifferentialGraded.Complex A) where
  obj X := complex A (FiniteBijection.card X)
  map f := sequenceMap A f
  map_id X := by
    simp only [sequenceMap_self, FiniteBijection.equivOfHom_id]
    exact complexRename_one A _
  map_comp {X Y Z} f g := by
    obtain rfl := FiniteBijection.object_eq_of_hom f
    obtain rfl := FiniteBijection.object_eq_of_hom g
    simp only [sequenceMap_self, FiniteBijection.equivOfHom_comp]
    exact complexRename_mul A _ _ _

/-- 概要：対称列の第 n 成分は構成した χ(n)（BF §1.2）。
方針：標準 n 元対象で関手を評価する。
規約：定義による等式。
使われ方：arity ごとの成分計算を対称列へ戻す。 -/
lemma sequence_level (n : ℕ) : SymmetricSequence.level (sequence A) n = complex A n := rfl

/-- 概要：対称列の置換像は値の複体上の左作用（BF §1.2.1）。
方針：骨格の置換射を自己射の公式で評価する。
規約：BE の共変な逆右作用と同じ規約となる。
使われ方：オペラッドの同変性と TR の自然性。 -/
lemma sequence_map_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (sequence A).map (FiniteBijection.permutation n σ) = complexRename A n σ := by
  rw [show (sequence A).map (FiniteBijection.permutation n σ) =
    sequenceMap A (FiniteBijection.permutation n σ) from rfl, sequenceMap_self]
  rfl

end SerrePositivity.EInfinity.Surjection
