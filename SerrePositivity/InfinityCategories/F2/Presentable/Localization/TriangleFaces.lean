module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ArrowCardinals
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeReindex

/-!
概要：元の二単体の全関手圏と、その三つの辺への制限を扱う。
方針：公開済みの関手圏の presentable 性と、全余錐の点ごとの制限を使う。
規約：元の二単体の全自然な族を保持する。
使われ方：HTT 5.5.4.14 の二対三則の同時 compact 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C]

/-- 宇宙変更を元の標準二単体へ戻した、三角形全体の関手圏の presentable 性。 -/
lemma triangle_isPresentable (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable ((ihom (Δ[2] : SSet.{u + 1})).obj C) :=
  (functor_isPresentable (Δ[2] : SSet.{u}) hC).of_equivalence
    ((qCatEquivalenceOfIso (uliftStdSimplexIso.{u, u + 1} 2)).precompose C).symm

/-- 三つの辺への各制限は、元の指定小余極限を保存する。 -/
lemma triangleFace_preservesSmallColimits (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (j : Fin 3) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits ((pre (stdSimplex.δ j)).app C) := by
  intro K D c hc
  exact isColimitCone_of_pointwise _
    ((isPointwiseColimitCone_of_hasColimits (hC K) c hc).reindex (stdSimplex.δ j))

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
