module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainDiagonal
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.ChainCoassociativity
public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Comultiplication

/-!
# 整数 AW 対角の余結合性

概要：Berger–Fresse §1.1.4 の AW 対角の余結合性を整数模型へ移す。
方針：負次数への移送が余結合性を保つ一般補題を適用する。
規約：既存の整数コチェインテンソルの結合子を使う。
使われ方：実際の E(n) 上の Hopf 対角の余結合性。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：整数 AW 対角は余結合的（Berger–Fresse §1.1.4）。
方針：鎖 AW 対角の余結合性をテンソル比較で移す。
規約：追加の有限性・平坦性・標数の仮定を置かない。
使われ方：E(n) の対角を Hopf オペラッドへ束ねる。 -/
lemma cochainDiagonal_coassoc (X : SSet.{0}) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X ≫
        HomologicalComplex.tensorHom (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X) (𝟙 (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)) ≫
        (HomologicalComplex.associator (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)).hom =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X ≫
        HomologicalComplex.tensorHom (𝟙 (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X) :=
  _root_.SerrePositivity.NegativeTensor.comultiplication_coassoc (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal_coassoc A X)

end SerrePositivity.SimplicialChains.AlexanderWhitney
