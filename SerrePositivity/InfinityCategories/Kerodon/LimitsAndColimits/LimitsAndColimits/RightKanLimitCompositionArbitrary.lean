module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RightKanLimitComposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.RightKanComparisonUniverse
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.RightKanTransportUniverseLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FunctorHomCongrEvaluation
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition

/-!
概要：指定右 Kan 変換に沿った元の全錐の比較は、任意の準圏係数で極限性を保ち反映する。
方針：同じ全錐の変換を全共変表現可能関手へ写し、空間値で極限を構成してから反映する。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の篩の交叉と降下。
規約：係数圏に極限存在や presentable 性を仮定しない。指定余単位と実際の全錐を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 元の実錐の固定頂点での比較と指定右 Kan 射から、任意の準圏値で極限性の同値を得る。 -/
lemma isLimitCone_iff_of_rightKan_comparison
    {I K D : SSet.{u}} [Quasicategory I] [Quasicategory K] [Quasicategory D]
    (δ : I ⟶ K) {p : K ⟶ D} {q : I ⟶ D} (c : JoinCone p) (d : JoinCone q)
    (α : SSet.Homotopy (δ ≫ p) q) (hα : IsRightKanExtension δ q p α)
    (H : SSet.Homotopy (restrictJoinCone c δ).val d.val)
    (hbase : (joinInr (Δ[0] : SSet.{u}) I ▷ (Δ[1] : SSet.{u})) ≫ H.h = α.h)
    (hfixed : (joinInl (Δ[0] : SSet.{u}) I ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ joinInl (Δ[0] : SSet.{u}) I ≫
        (restrictJoinCone c δ).val) :
    IsLimitCone c ↔ IsLimitCone d := by
  rw [isLimitCone_iff_covariantRepresentableInfinity c,
    isLimitCone_iff_covariantRepresentableInfinity d]
  apply forall_congr'
  intro x
  exact rightKanComparisonUliftPostcomp_isLimit_iff δ c d H α hbase hfixed
    (covariantRepresentableInfinity x) (space_hasSmallLimits K _) (space_hasSmallLimits I _)
    (kanRightKanExtension_covariantRepresentable hα x)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
