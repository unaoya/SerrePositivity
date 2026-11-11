module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.RepresentableRetractions
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.FullSubcomplexSplitting
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：κ-compact 対象の全部分 ∞ 圏と、その coherent 冪等完備性を構成。
方針：証明済みの retract 閉性と元の全分裂の全部分圏への反映を使う。
規約：Ind の単一 filtered 表示や Yoneda 像の compact 性をここで仮定しない。
使われ方：Ind の compact 部分と Idem(C) の全 ∞ 圏としての比較。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects


/-- 小さい κ-filtered 添字について compact な対象の、元の圏の全部分 ∞ 圏。 -/
@[kerodon 064F]
def kappaCompactObjects (κ : Cardinal.{u}) (C : SSet.{max u v}) [Quasicategory C] :
    SSet.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ)

/-- κ-compact 対象は元の全辺・全高次を保持する quasicategory をなす。 -/
instance kappaCompactObjects_quasicategory (κ : Cardinal.{u}) (C : SSet.{max u v})
    [Quasicategory C] : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, v} κ C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 元の圏への κ-compact 全部分圏の包含。 -/
def kappaCompactInclusion (κ : Cardinal.{u}) (C : SSet.{max u v}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, v} κ C ⟶ C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ)).ι

/-- 元の包含は全写像空間で充満忠実。 -/
lemma kappaCompactInclusion_isFullyFaithful (κ : Cardinal.{u}) (C : SSet.{max u v})
    [Quasicategory C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (kappaCompactInclusion.{u, v} κ C) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _

/-- 冪等完備な元の圏の κ-compact 全部分圏は、全 coherent 分裂について冪等完備。 -/
lemma kappaCompactObjects_isIdempotentComplete (κ : Cardinal.{u})
    {C : SSet.{max u v}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (kappaCompactObjects.{u, v} κ C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.fullSubcomplex_isIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ)
    (fun r hy ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.of_retract r hy) hC

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
