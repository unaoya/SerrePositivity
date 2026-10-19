module

public import SerrePositivity.EInfinity.Shuffle.ChainCoalgebra
public import SerrePositivity.EInfinity.NegativeTensor.BinaryMap
public import SerrePositivity.EInfinity.AlexanderWhitney.CochainDiagonal

/-!
# 一般 shuffle の整数コチェイン模型

概要：Berger–Fresse §1.1.3–§1.1.4 の shuffle と AW 余積適合性を負の整数次数へ移す。
方針：標準テンソル比較の逆と零延長を用い、二入力写像の移送定理を適用する。
規約：既存の normalizedFunctor と同じ複体と標準の Koszul テンソルを使う。
使われ方：BE の既存の部分合成の AW 余積適合性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Shuffle

open CategoryTheory MonoidalCategory HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：一般 shuffle の整数コチェイン鎖写像（BF §1.1.3）。
方針：一般の自然数鎖写像を標準テンソル比較で移す。
規約：入力・出力は既存の正規化コチェイン関手の対象。
使われ方：BE 部分合成との生成元上の比較。 -/
def cochainMap (X Y : SSet.{0}) :
    AlexanderWhitney.cochains A X ⊗ AlexanderWhitney.cochains A Y ⟶
      AlexanderWhitney.cochains A (X ⊗ Y) :=
  NegativeTensor.binaryMap (chainMap A X Y)

/-- 概要：整数模型の一般 shuffle は AW 余積を保つ（BF §1.1.4）。
方針：一般の二入力写像の余積適合性の移送定理を使う。
規約：中間二因子には整数コチェインの実際の符号付き交換を用いる。
使われ方：BE 部分合成と Hopf 対角の可換性。 -/
lemma cochainMap_diagonal (X Y : SSet.{0}) :
    cochainMap A X Y ≫ AlexanderWhitney.cochainDiagonal A (X ⊗ Y) =
      HomologicalComplex.tensorHom (AlexanderWhitney.cochainDiagonal A X)
          (AlexanderWhitney.cochainDiagonal A Y) ≫
        (SerrePositivity.cochainTensorShuffle (AlexanderWhitney.cochains A X)
          (AlexanderWhitney.cochains A X) (AlexanderWhitney.cochains A Y)
          (AlexanderWhitney.cochains A Y)).hom ≫
        HomologicalComplex.tensorHom (cochainMap A X Y) (cochainMap A X Y) :=
  NegativeTensor.binaryMap_comultiplication (AlexanderWhitney.diagonal A X)
    (AlexanderWhitney.diagonal A Y) (AlexanderWhitney.diagonal A (X ⊗ Y))
    (chainMap A X Y) (chainMap_diagonal A X Y)

end SerrePositivity.EInfinity.Shuffle
