module

public import SerrePositivity.EInfinity.Operad.ConvolutionInsertionEvaluation
public import SerrePositivity.EInfinity.Operad.ConvolutionAssemblyComposition
public import SerrePositivity.EInfinity.Operad.HopfComponents

/-!
# Convolution の部分合成

概要：Berger–Fresse §3.1 の convolution の先頭位置の部分合成公理を証明する。
方針：二段の評価図式をまとめ、Hopf 対角と代数・余代数の合成則を使う。
規約：全入力数を扱い、始域の cofibrancy を要求しない。
使われ方：先頭位置での判定から内部 Hom の P 代数を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- 概要：Hopf 対角は二つの係数の分配と部分合成を保つ（BM §1、BF §3.1）。
方針：対角のオペラッド射性を Hadamard 積の部分合成の定義で展開する。
規約：二列に同じ入力位置を使う。
使われ方：convolution の評価を代数・余代数の合成則へ移す。 -/
lemma convolutionDiagonal_comp (hP : Hopf P) (m n : ℕ) (i : Fin (m + 1)) :
    P.comp m n i ≫ hP.diagonalComponent (m + n) =
    ((hP.diagonalComponent (m + 1) ⊗ₘ
      hP.diagonalComponent n) ≫
      tensorμ (P.arity (m + 1)) (P.arity (m + 1)) (P.arity n) (P.arity n)) ≫
      (P.comp m n i ⊗ₘ P.comp m n i) := by
  rw [Category.assoc]
  exact hP.diagonal.comp m n i

/-- 概要：評価後の先頭部分合成は convolution 演算の代入に一致する（BF §3.1）。
方針：二段の組み立てを一段へまとめ、対角・余演算・作用の合成則を適用する。
規約：入力への代入と出力への余代入は標準の先頭射で表す。
使われ方：右 tensor 転置を戻して convolution の部分合成公理を得る。 -/
lemma convolutionUncurriedAction_comp_zero (hP : Hopf P) (H : P.Coalgebra)
    (B : P.Algebra) (m n : ℕ) :
    ((P.comp m n 0 ▷ power (homComplex A H.carrier B.carrier) (m + n)) ▷ H.carrier) ≫
      convolutionUncurriedAction hP H B (m + n) =
    ((α_ (P.arity (m + 1)) (P.arity n)
      (power (homComplex A H.carrier B.carrier) (m + n))).hom ▷ H.carrier) ≫
      ((P.arity (m + 1) ◁
        tensorInsertionAction (homComplex A H.carrier B.carrier) (P.arity n) m n 0
          (convolutionAction hP H B n)) ▷ H.carrier) ≫
      convolutionUncurriedAction hP H B (m + 1) := by
  exact convolutionAssembly_composition_of_maps
    (hP.diagonalComponent (m + 1))
    (hP.diagonalComponent n) (H.coaction (m + 1))
    (tensorCoInsertionAction H.carrier (P.arity n) m n 0 (H.coaction n))
    (convolutionPowerEvaluation H.carrier B.carrier (m + n))
    (tensorInsertionAction B.carrier (P.arity n) m n 0 (B.action n)) (B.action (m + 1))
    (hP.diagonalComponent (m + n)) (H.coaction (m + n))
    (B.action (m + n)) (P.comp m n 0) (P.comp m n 0) (P.comp m n 0)
    (convolutionPowerEvaluation H.carrier B.carrier (m + 1))
    (tensorInsertionAction (homComplex A H.carrier B.carrier) (P.arity n) m n 0
      (convolutionAction hP H B n))
    (convolutionDiagonal_comp hP m n 0) (H.comp_coaction m n 0) (B.comp_action m n 0)
    (convolutionAction_insertion_zero_evaluation hP H B m n)

end SerrePositivity.EInfinity.Operad
