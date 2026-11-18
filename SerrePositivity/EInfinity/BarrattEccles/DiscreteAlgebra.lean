module

public import SerrePositivity.EInfinity.BarrattEccles.OperadAugmentation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraRestriction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.DiscreteCommutative

/-!
# 離散可換代数の実際の E 代数構造

概要：BF §1・BM §1 の E → Com に沿って離散可換代数を E 代数にする。
方針：零次複体上の全入力の Com 作用を実際の augmentation で制限する。
規約：任意の可換基礎環、arity 零を含む。底の複体と射を保持する。
使われ方：E2a-4 の離散可換代数と E2b の離散対象の供給。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory
open SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：離散可換 A 代数を実際の E 代数にする関手（BF §1、BM §1）。
方針：零次複体の Com 代数化と E → Com に沿う制限を合成する。
規約：元の単位・積と底の複体・射を使い、全 arity を含む。
使われ方：E2a-4 の離散可換代数と E2b の離散対象。 -/
def discreteAlgebraFunctor : CommAlgCat.{u} A ⥤ (operad A).Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.discreteCommutativeFunctor A ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebra (augmentation A)

/-- 概要：離散 E 代数の底は元の加群の零次複体（BF §1）。
方針：二つの関手の対象成分を評価する。
規約：底の複体を同型だけでなく厳密に同定する。
使われ方：離散 E 代数のコホモロジーの計算。 -/
lemma discreteAlgebraFunctor_carrier (B : CommAlgCat.{u} A) :
    ((discreteAlgebraFunctor A).obj B).carrier =
      SerrePositivity.cochainSingleZero (ModuleCat.of A B) := rfl

/-- 概要：離散 E 代数射の底は元の代数射の零次複体への埋め込み（BF §1）。
方針：可換モノイド・Com・E の三つの関手の射成分を評価する。
規約：元の A 線形写像を保持する。
使われ方：離散対象の忘却後の関手性の比較。 -/
lemma discreteAlgebraFunctor_map {B D : CommAlgCat.{u} A} (f : B ⟶ D) :
    ((discreteAlgebraFunctor A).map f).hom =
      (CochainComplex.singleFunctor (ModuleCat A) 0).map
        (ModuleCat.ofHom f.hom.toLinearMap) := rfl

/-- 概要：離散 E 代数の作用は実際の E → Com の制限（BF §1、BM §1）。
方針：制限の定義を展開する。
規約：零入力を含む全 arity。
使われ方：演算を元の可換代数の反復積へ帰着する。 -/
lemma discreteAlgebraFunctor_action (B : CommAlgCat.{u} A) (n : ℕ) :
    ((discreteAlgebraFunctor A).obj B).action n =
      ((augmentation A).map.app (FiniteBijection.of n) ▷
        power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.discreteCommutativeFunctor A).obj B).carrier n) ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.discreteCommutativeFunctor A).obj B).action n := rfl

end SerrePositivity.EInfinity.BarrattEccles
