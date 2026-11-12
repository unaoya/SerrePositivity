module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FlipFunctorHom

/-!
概要：関手の変数交換による Hom 同値の合成保存。
方針：ホモトピー圏の交換関手の合成保存を使う。
規約：指定した全 Hom を保持する。
使われ方：余極限単位の標準 Hom 公式の交換。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の Hom の変数交換は合成を保つ。
方針：交換同型のホモトピー圏の関手性を使う。
規約：元の三つの関手を保持する。
使われ方：随伴の単位による Hom 写像の比較。 -/
lemma flipFunctorHomEquiv_comp {A B X : SSet.{u}} [Quasicategory X]
    {U V W : A ⟶ (ihom B).obj X} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.flipFunctorHomEquiv U W (α ≫ β) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.flipFunctorHomEquiv U V α ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.flipFunctorHomEquiv V W β :=
  (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A B X).hom).toFunctor.map_comp α β

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
