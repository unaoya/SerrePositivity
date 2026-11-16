module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanTransportComparisonFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport

/-!
概要：指定余単位に両立する同じ全関手の同型に沿って、元の右Kan延長条件を移す。
方針：既存の輸送の終点比較を使い、実際の錐の関手圏で終対象性を移す。
規約：HTT §4.3.2、Kerodon §7.3（Tag 02Y1）の既存構成の係数移送の法則。
使われ方：S8 の元の大域比較から同じ指定余単位のKan条件を得る。Hom普遍性だけで代替しない。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 元の指定余単位の類と両立する全関手同型に沿って、実際の右Kan条件を移す。 -/
lemma isRightKanExtension_of_compatible_functorIso
    {K C D : SSet.{u}} [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) (β : SSet.Homotopy (δ ≫ G) F₀)
    (η : FunctorIso F G)
    (hη : rightKanHomMap δ (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy β)) F η.hom =
        Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α))
    (hα : IsRightKanExtension δ F₀ F α) : IsRightKanExtension δ F₀ G β := by
  intro c
  obtain ⟨t, ht⟩ := hα c
  obtain ⟨s⟩ := rightKanConeTransport_nonempty δ F₀ G β c
  obtain ⟨i, _⟩ := rightKanTransport_comparison_factorization α β η hη c t s
  refine ⟨s, (isLimitCone_iff_isTerminalVertex_coneFamily s.cone).mpr ?_⟩
  exact (isTerminalVertex_iff_of_vertexIso i).mp
    ((isLimitCone_iff_isTerminalVertex_coneFamily t.cone).mp ht)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
