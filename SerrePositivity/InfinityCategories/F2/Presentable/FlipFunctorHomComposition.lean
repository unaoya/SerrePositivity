module

public import SerrePositivity.InfinityCategories.F2.Presentable.FlipFunctorHom

/-!
概要：関手の変数交換による Hom 同値の合成保存。
方針：ホモトピー圏の交換関手の合成保存を使う。
規約：指定した全 Hom を保持する。
使われ方：余極限単位の標準 Hom 公式の交換。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の Hom の変数交換は合成を保つ。
方針：交換同型のホモトピー圏の関手性を使う。
規約：元の三つの関手を保持する。
使われ方：随伴の単位による Hom 写像の比較。 -/
lemma flipFunctorHomEquiv_comp {A B X : SSet.{u}} [Quasicategory X]
    {U V W : A ⟶ (ihom B).obj X} (α : FunctorHom U V) (β : FunctorHom V W) :
    flipFunctorHomEquiv U W (α ≫ β) =
      flipFunctorHomEquiv U V α ≫ flipFunctorHomEquiv V W β :=
  (hoFunctor.map (internalHomSwapIso A B X).hom).toFunctor.map_comp α β

end SerrePositivity.InfinityCategories.F2.Presentable
