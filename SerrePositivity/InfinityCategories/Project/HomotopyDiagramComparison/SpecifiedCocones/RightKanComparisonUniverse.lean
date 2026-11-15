module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.ConeHomotopyUniverseComponents
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FunctorHomCongrEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RightKanLimitComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightHomUniversal

/-!
概要：元の右 Kan 比較の全錐の変換を、宇宙移送した実制限錐からの射として固定する。
方針：全錐の制限の等式で始域だけを正規化し、元の底と固定頂点の法則を移す。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の任意の係数での降下。
規約：大きい本文を展開しないため、指定変換を名前付きの同じ射として保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の全錐間の変換を、移送した実際の制限錐から始まる同じ射として固定する。 -/
def rightKanComparisonUliftPostcompHom {I K D : SSet.{u}} {p : K ⟶ D} {q : I ⟶ D}
    (δ : I ⟶ K) (c : JoinCone p) (d : JoinCone q)
    (H : SSet.Homotopy (restrictJoinCone c δ).val d.val)
    {E : SSet.{max u v}} (U : (SSet.uliftFunctor.{v, u}).obj D ⟶ E) :
    FunctorHom (restrictJoinCone (mapJoinCone U (JoinCone.ulift.{u, v} c))
      ((SSet.uliftFunctor.{v, u}).map δ)).val (mapJoinCone U (JoinCone.ulift.{u, v} d)).val :=
  kanFunctorHomCongr (restrictJoinCone_ulift_postcomp_val c δ U) rfl
    (coneHomotopyUliftPostcompHom H U)

/-- 移送した実制限錐からの同じ射は、元の固定した頂点で可逆。 -/
lemma rightKanComparisonUliftPostcompHom_apex_isIso
    {I K D : SSet.{u}} {p : K ⟶ D} {q : I ⟶ D}
    (δ : I ⟶ K) (c : JoinCone p) (d : JoinCone q)
    (H : SSet.Homotopy (restrictJoinCone c δ).val d.val)
    (hfixed : (joinInl (Δ[0] : SSet.{u}) I ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ joinInl (Δ[0] : SSet.{u}) I ≫
        (restrictJoinCone c δ).val)
    {E : SSet.{max u v}} (U : (SSet.uliftFunctor.{v, u}).obj D ⟶ E) :
    IsIso (functorHomEvaluate (rightKanComparisonUliftPostcompHom δ c d H U)
      (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj I)))) := by
  apply (kanFunctorHomCongr_evaluate_isIso_iff _ _ _ _).mpr
  exact coneHomotopyUliftPostcompHom_apex_isIso H hfixed U

/-- 実制限錐の表示へ揃えた同じ全変換の底も、元の指定右 Kan 余単位と一致。 -/
lemma rightKanComparisonUliftPostcompHom_boundary
    {I K D : SSet.{u}} {p : K ⟶ D} {q : I ⟶ D}
    (δ : I ⟶ K) (c : JoinCone p) (d : JoinCone q)
    (H : SSet.Homotopy (restrictJoinCone c δ).val d.val)
    (α : SSet.Homotopy (δ ≫ p) q)
    (hbase : (joinInr (Δ[0] : SSet.{u}) I ▷ (Δ[1] : SSet.{u})) ≫ H.h = α.h)
    {E : SSet.{max u v}} (U : (SSet.uliftFunctor.{v, u}).obj D ⟶ E) :
    kanFunctorHomCongr
      (restrictJoinCone (mapJoinCone U (JoinCone.ulift.{u, v} c))
        ((SSet.uliftFunctor.{v, u}).map δ)).property
      (mapJoinCone U (JoinCone.ulift.{u, v} d)).property
      ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{max u v})
        ((SSet.uliftFunctor.{v, u}).obj I))).app E)).toFunctor.map
          (rightKanComparisonUliftPostcompHom δ c d H U)) =
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (kanRightCounitPostcomp (kanRightCounitUlift.{u, v} α) U)) := by
  apply Arrow.mk_injective
  rw [kanFunctorHomCongr_arrow]
  change (hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{max u v})
    ((SSet.uliftFunctor.{v, u}).obj I))).app E)).toFunctor.mapArrow.obj
      (Arrow.mk (rightKanComparisonUliftPostcompHom δ c d H U)) = _
  rw [rightKanComparisonUliftPostcompHom, kanFunctorHomCongr_arrow]
  exact coneHomotopyUliftPostcompHom_boundary_arrow H α hbase U

/-- 同じ移送した係数で両極限が存在する場合は、元の指定比較から極限性を比較できる。 -/
lemma rightKanComparisonUliftPostcomp_isLimit_iff
    {I K D : SSet.{u}} [Quasicategory I] [Quasicategory K]
    {p : K ⟶ D} {q : I ⟶ D} (δ : I ⟶ K) (c : JoinCone p) (d : JoinCone q)
    (H : SSet.Homotopy (restrictJoinCone c δ).val d.val)
    (α : SSet.Homotopy (δ ≫ p) q)
    (hbase : (joinInr (Δ[0] : SSet.{u}) I ▷ (Δ[1] : SSet.{u})) ≫ H.h = α.h)
    (hfixed : (joinInl (Δ[0] : SSet.{u}) I ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ joinInl (Δ[0] : SSet.{u}) I ≫
        (restrictJoinCone c δ).val)
    {E : SSet.{max u v}} [Quasicategory E] (U : (SSet.uliftFunctor.{v, u}).obj D ⟶ E)
    (hp : HasLimit ((SSet.uliftFunctor.{v, u}).map p ≫ U))
    (hq : HasLimit ((SSet.uliftFunctor.{v, u}).map q ≫ U))
    (hα : IsRightKanExtension ((SSet.uliftFunctor.{v, u}).map δ)
      ((SSet.uliftFunctor.{v, u}).map q ≫ U) ((SSet.uliftFunctor.{v, u}).map p ≫ U)
      (kanRightCounitPostcomp (kanRightCounitUlift.{u, v} α) U)) :
    IsLimitCone (mapJoinCone U (JoinCone.ulift.{u, v} c)) ↔
      IsLimitCone (mapJoinCone U (JoinCone.ulift.{u, v} d)) := by
  haveI := rightKanComparisonUliftPostcompHom_apex_isIso δ c d H hfixed U
  apply isLimitCone_iff_of_rightKan_comparison_with_limits ((SSet.uliftFunctor.{v, u}).map δ)
    hp hq (mapJoinCone U (JoinCone.ulift.{u, v} c)) (mapJoinCone U (JoinCone.ulift.{u, v} d))
    (rightKanComparisonUliftPostcompHom δ c d H U)
  rw [rightKanComparisonUliftPostcompHom_boundary δ c d H α hbase U]
  exact kanRightKanExtension_homUniversal _ _ hα

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
