module

public import SerrePositivity.InfinityCategories.Core.InternalHomFlipAdjunction
public import SerrePositivity.InfinityCategories.Core.InternalHomSwap
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomCorrespondence

/-!
概要：二重関手圏の変数交換を元の関手間の Hom 同値として保持する。
方針：内部 Hom の交換同型の充満忠実性を使う。
規約：元の両端の転置を使う。
使われ方：余極限単位の全パラメータ Hom 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：変数交換による元の関手間の射の同値。
方針：交換同型のホモトピー圏の Hom 作用を使う。
規約：始域の充填性は不要。
使われ方：全余錐の普遍性と指定単位の対応。 -/
def flipFunctorHomEquiv {A B X : SSet.{u}} [Quasicategory X]
    (U V : A ⟶ (ihom B).obj X) : FunctorHom U V ≃
      FunctorHom (internalHomFlipHomEquiv A B X U) (internalHomFlipHomEquiv A B X V) :=
  (qCatEquivalenceOfIso (internalHomSwapIso A B X)).isFullyFaithful.toHoFullyFaithful.homEquiv

end SerrePositivity.InfinityCategories.F2.Presentable
