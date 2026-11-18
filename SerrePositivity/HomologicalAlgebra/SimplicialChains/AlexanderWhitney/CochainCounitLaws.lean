module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCounit
public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Counit

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

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：整数 AW 対角の左余単位則（Berger–Fresse §1.1.4）。
方針：鎖対角の左余単位則を標準のテンソル比較で移す。
規約：既存の整数複体の左単位子を使う。
使われ方：E → Com を Hopf 対角の左余単位として使う。 -/
lemma cochainDiagonal_left_counit (X : SSet.{0}) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X ≫
        HomologicalComplex.tensorHom (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A X) (𝟙 (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)) ≫
        (HomologicalComplex.leftUnitor (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)).hom = 𝟙 _ :=
  _root_.SerrePositivity.NegativeTensor.comultiplication_left_counit (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A X)
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal_left_counit A X)

/-- 概要：整数 AW 対角の右余単位則（Berger–Fresse §1.1.4）。
方針：鎖対角の右余単位則を標準のテンソル比較で移す。
規約：既存の整数複体の右単位子を使う。
使われ方：E → Com を Hopf 対角の右余単位として使う。 -/
lemma cochainDiagonal_right_counit (X : SSet.{0}) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X ≫
        HomologicalComplex.tensorHom (𝟙 (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A X) ≫
        (HomologicalComplex.rightUnitor (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)).hom = 𝟙 _ :=
  _root_.SerrePositivity.NegativeTensor.comultiplication_right_counit (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A X)
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal_right_counit A X)

end SerrePositivity.SimplicialChains.AlexanderWhitney
