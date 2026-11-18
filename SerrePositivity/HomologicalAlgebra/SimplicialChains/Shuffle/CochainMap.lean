module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.ChainCoalgebra
public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.BinaryMap
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainDiagonal

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

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：一般 shuffle の整数コチェイン鎖写像（BF §1.1.3）。
方針：一般の自然数鎖写像を標準テンソル比較で移す。
規約：入力・出力は既存の正規化コチェイン関手の対象。
使われ方：BE 部分合成との生成元上の比較。 -/
def cochainMap (X Y : SSet.{0}) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X ⊗ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A Y ⟶
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A (X ⊗ Y) :=
  _root_.SerrePositivity.NegativeTensor.binaryMap (_root_.SerrePositivity.SimplicialChains.Shuffle.chainMap A X Y)

/-- 概要：整数模型の一般 shuffle は AW 余積を保つ（BF §1.1.4）。
方針：一般の二入力写像の余積適合性の移送定理を使う。
規約：中間二因子には整数コチェインの実際の符号付き交換を用いる。
使われ方：BE 部分合成と Hopf 対角の可換性。 -/
lemma cochainMap_diagonal (X Y : SSet.{0}) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.cochainMap A X Y ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A (X ⊗ Y) =
      HomologicalComplex.tensorHom (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X)
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A Y) ≫
        (SerrePositivity.cochainTensorShuffle (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A Y)
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A Y)).hom ≫
        HomologicalComplex.tensorHom (_root_.SerrePositivity.SimplicialChains.Shuffle.cochainMap A X Y) (_root_.SerrePositivity.SimplicialChains.Shuffle.cochainMap A X Y) :=
  _root_.SerrePositivity.NegativeTensor.binaryMap_comultiplication (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X)
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A Y) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A (X ⊗ Y))
    (_root_.SerrePositivity.SimplicialChains.Shuffle.chainMap A X Y) (_root_.SerrePositivity.SimplicialChains.Shuffle.chainMap_diagonal A X Y)

end SerrePositivity.SimplicialChains.Shuffle
