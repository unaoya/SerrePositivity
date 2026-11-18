module

public import SerrePositivity.EInfinity.BarrattEccles.GeneralShuffleComparison
public import SerrePositivity.EInfinity.BarrattEccles.ComplexDiagonal
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle

/-!
# BE 部分合成と AW 対角の可換性

概要：Berger–Fresse §1.1.4 の Hopf 合成則を実際の BE 部分合成について証明する。
方針：一般 shuffle の余積適合性と単体的部分合成に対する AW の自然性を合成する。
規約：二つの対角の間の交換は既存の整数コチェインの Koszul 交換。
使われ方：arity ごとのテンソルオペラッドへの Hopf 対角の射性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：既存の BE 部分合成は AW 余積を保つ（BF §1.1.4）。
方針：部分合成を一般 shuffle と単体的合成に分解して二つの可換性を適用する。
規約：arity 0 の内側演算も含め、追加の cofibrancy を仮定しない。
使われ方：Hopf 対角のオペラッド射性の部分合成条件。 -/
lemma partialComposition_diagonal (m n : ℕ) (i : Fin (m + 1)) :
    partialComposition A m n i ≫ complexDiagonal A (m + n) =
      HomologicalComplex.tensorHom (complexDiagonal A (m + 1)) (complexDiagonal A n) ≫
        (SerrePositivity.cochainTensorShuffle (complex A (m + 1)) (complex A (m + 1))
          (complex A n) (complex A n)).hom ≫
        HomologicalComplex.tensorHom (partialComposition A m n i) (partialComposition A m n i) := by
  simp only [partialComposition_eq_generalShuffle, complexDiagonal]
  rw [Category.assoc, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_natural]
  rw [← Category.assoc, _root_.SerrePositivity.SimplicialChains.Shuffle.cochainMap_diagonal]
  change _ = _ ≫ _ ≫
    ((_root_.SerrePositivity.SimplicialChains.Shuffle.cochainMap A (simplicial (m + 1)) (simplicial n) ≫
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A (simplicialPartialComposition m n i)) ⊗ₘ
      (_root_.SerrePositivity.SimplicialChains.Shuffle.cochainMap A (simplicial (m + 1)) (simplicial n) ≫
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A (simplicialPartialComposition m n i)))
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rfl

private lemma cochainShuffle_eq_tensorμ (P Q T U : CochainComplex (ModuleCat.{u} A) ℤ) :
    (SerrePositivity.cochainTensorShuffle P Q T U).hom = tensorμ P Q T U := rfl

/-- 概要：BE 合成の余積適合性を標準の tensorμ で述べる（BF §1.1.4）。
方針：四因子の交換同型と対称モノイダル構造の tensorμ の定義の一致を使う。
規約：arity ごとのテンソルオペラッドが使う標準の射を明示する。
使われ方：Hopf 対角の部分合成条件。 -/
lemma partialComposition_diagonal_tensorμ (m n : ℕ) (i : Fin (m + 1)) :
    partialComposition A m n i ≫ complexDiagonal A (m + n) =
      (complexDiagonal A (m + 1) ⊗ₘ complexDiagonal A n) ≫
        tensorμ (complex A (m + 1)) (complex A (m + 1)) (complex A n) (complex A n) ≫
        (partialComposition A m n i ⊗ₘ partialComposition A m n i) := by
  have he := partialComposition_diagonal A m n i
  rw [cochainShuffle_eq_tensorμ] at he
  convert he using 1

end SerrePositivity.EInfinity.BarrattEccles
