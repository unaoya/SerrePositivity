module

public import SerrePositivity.EInfinity.AlexanderWhitney.CochainCounit
public import SerrePositivity.EInfinity.NegativeTensor.Counit

/-!
# 整数 AW 対角の余単位則

概要：Berger–Fresse §1.1.4 の AW 対角と augmentation の左右余単位則を整数模型で述べる。
方針：鎖対角の余単位則に負次数への移送の一般補題を適用する。
規約：単位子・augmentation とも既存の整数コチェイン模型を使う。
使われ方：E の Hopf 対角の余単位則。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.AlexanderWhitney

open CategoryTheory MonoidalCategory HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：整数 AW 対角の左余単位則（Berger–Fresse §1.1.4）。
方針：鎖対角の左余単位則を標準のテンソル比較で移す。
規約：既存の整数複体の左単位子を使う。
使われ方：E → Com を Hopf 対角の左余単位として使う。 -/
lemma cochainDiagonal_left_counit (X : SSet.{0}) :
    cochainDiagonal A X ≫
        HomologicalComplex.tensorHom (cochainCounit A X) (𝟙 (cochains A X)) ≫
        (HomologicalComplex.leftUnitor (cochains A X)).hom = 𝟙 _ :=
  NegativeTensor.comultiplication_left_counit (chains A X) (diagonal A X) (counit A X)
    (diagonal_left_counit A X)

/-- 概要：整数 AW 対角の右余単位則（Berger–Fresse §1.1.4）。
方針：鎖対角の右余単位則を標準のテンソル比較で移す。
規約：既存の整数複体の右単位子を使う。
使われ方：E → Com を Hopf 対角の右余単位として使う。 -/
lemma cochainDiagonal_right_counit (X : SSet.{0}) :
    cochainDiagonal A X ≫
        HomologicalComplex.tensorHom (𝟙 (cochains A X)) (cochainCounit A X) ≫
        (HomologicalComplex.rightUnitor (cochains A X)).hom = 𝟙 _ :=
  NegativeTensor.comultiplication_right_counit (chains A X) (diagonal A X) (counit A X)
    (diagonal_right_counit A X)

end SerrePositivity.EInfinity.AlexanderWhitney
