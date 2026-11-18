module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Hopf
public import SerrePositivity.EInfinity.BarrattEccles.DiagonalUnit
public import SerrePositivity.EInfinity.BarrattEccles.OperadAugmentation

/-!
# Barratt–Eccles の Hopf オペラッド構造

概要：Berger–Fresse §1.1.4 の AW 対角を Hopf dg オペラッド構造に束ねる。
方針：自然性・単位と部分合成の保存・既存の余代数則を同じ対角へ接続する。
規約：任意の可換基礎環を扱い、余単位は既存の E → Com とする。
使われ方：E2a-3 の区間と path object による転送経路の Hopf 入力となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory

variable (A : Type u) [CommRing A]

/-- 概要：AW 対角は BE 対称列の自然変換である（Berger–Fresse §1.1.4）。
方針：単体的対称列の各構造射へ一般 AW の自然性を適用する。
規約：有限全単射について自然であり、arity 0 も含む。
使われ方：Hopf 対角の底の対称列射となる。 -/
def diagonalSequence : (operad A).sequence ⟶
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.hadamard (operad A) (operad A)).sequence where
  app S := complexDiagonal A (FiniteBijection.card S)
  naturality {S T} f := by
    change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A (simplicialSequenceMap f) ≫
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A (simplicial (FiniteBijection.card T)) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A (simplicial (FiniteBijection.card S)) ≫ _
    exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_natural A (simplicialSequenceMap f)

/-- 概要：AW 対角は E → E ⊗ E のオペラッド射である（Berger–Fresse §1.1.4）。
方針：対称列の自然性と単位・全ての部分合成の保存を束ねる。
規約：終域は構成済みの Hadamard オペラッド。
使われ方：E 代数のテンソルと E-coalgebra 区間に演算を分配する。 -/
def hopfDiagonal : operad A ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.hadamard (operad A) (operad A) where
  map := diagonalSequence A
  unit := unit_diagonal A
  comp m n i := by
    change partialComposition A m n i ≫ complexDiagonal A (m + n) =
      (complexDiagonal A (m + 1) ⊗ₘ complexDiagonal A n) ≫
        (tensorμ _ _ _ _ ≫ (partialComposition A m n i ⊗ₘ partialComposition A m n i))
    simpa only [Category.assoc] using partialComposition_diagonal_tensorμ A m n i

/-- 概要：Hopf 対角の arity 成分は既存の AW 対角に一致する（BF §1.1.4）。
方針：射と自然変換を標準 n 元対象で評価する。
規約：定義による等式である。
使われ方：余代数の法則とオペラッド射を接続する。 -/
lemma hopfDiagonal_app (n : ℕ) :
    (hopfDiagonal A).map.app (FiniteBijection.of n) = complexDiagonal A n := rfl

/-- 概要：Barratt–Eccles の余単位付き Hopf dg オペラッド構造（BF §1.1.4）。
方針：実際の AW オペラッド射と既存の augmentation に余代数則を束ねる。
規約：任意の可換基礎環で定義し、余可換性は要求しない。
使われ方：E-coalgebra 区間からの path object とモデル構造の転送。 -/
def hopf : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf (operad A) where
  diagonal := hopfDiagonal A
  counit := augmentation A
  coassoc n := complexDiagonal_coassoc A n
  left_counit n := complexDiagonal_left_counit A n
  right_counit n := complexDiagonal_right_counit A n

end SerrePositivity.EInfinity.BarrattEccles
