module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SmallMarkedFactorization
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseMorphismUp
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences

/-!
概要：元の局所化に沿って、任意の大きい標的への反転関手を延長する。
方針：同じ反転関手を小模型へ因子化し、小さい普遍性の実延長と同型を持ち上げる。
規約：局所化の源・標的の quasicategory 性は追加しない。
使われ方：Ind-S (4) の順方向の延長成分。充満忠実性は別葉で扱う。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization


/-- 元の局所化の全反転関手の延長は、任意の大きい quasicategory を標的にして存在する。 -/
theorem IsLocalization.exists_extension_ulift {X D : SSet.{u}} {F : X ⟶ D}
    {W : Set (X _⦋1⦌)} (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W) {E : SSet.{max u v}}
    [Quasicategory E] (L : (SSet.uliftFunctor.{v, u}).obj X ⟶ E)
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges L (ULift.up.{v, u} '' W)) :
    ∃ G : (SSet.uliftFunctor.{v, u}).obj D ⟶ E,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{v, u}).map F ≫ G) L) := by
  obtain ⟨Q, hQ, l, j, _, hl, hW⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_small_inverting_factorization L W hL
  letI := hQ
  obtain ⟨g, ⟨e⟩⟩ := hF.exists_extension l hW
  refine ⟨(SSet.uliftFunctor.{v, u}).map g ≫ j, ⟨?_⟩⟩
  have e' := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functorIso_ulift.{u, v} e).postcomp j
  simpa only [Functor.map_comp, Category.assoc, hl] using e'

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
