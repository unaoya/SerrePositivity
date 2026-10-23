module

public import SerrePositivity.InfinityCategories.F2.Presentable.RelativeHomModel
public import SerrePositivity.InfinityCategories.F2.Presentable.KanTerminalHomComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.FullyFaithfulHomComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallKanHomAccessible
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseColimits
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseCoconePostcomposition
public import SerrePositivity.InfinityCategories.F1.UniverseQCatEquivalence

/-!
概要：小さい Kan 空間の compact 性を、N の元の大きい全共変 Hom の定義で証明する。
方針：終対象上の充満忠実な豊穣埋め込みと相対 Hom の分類を合成し、小さい全内部 Hom の宇宙変更へ比較する。
規約：全自然同型と指定全余錐を保持。compact 性や Hom 比較を追加の instance 仮定にしない。
使われ方：空間・前層の小さい compact 生成圏。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の大きい全共変 Hom を、同じ小さい Kan 内部 Hom の宇宙変更と全自然に比較する。 -/
def kanHom_covariantModelIso (K : KanObject.{u}) :
    FunctorIso (covariantRepresentableInfinity (C := SpaceInfinity.{u}) (coherentNerveVertex K))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (kanInternalHomInfinity K) ≫
        Compact.spaceUniverseDiagram.{u}) := by
  have h := covariantHomComparisonIso kanTerminalInfinity kanTerminalInfinity_isFullyFaithful
    (coherentNerveVertex K)
  change FunctorIso _ ((SSet.uliftFunctor.{u + 2, u + 1}).map kanTerminalInfinity ≫
    covariantRepresentableInfinity ((coherentNerveMap kanTerminalEnriched).app _
      (coherentNerveVertex K))) at h
  rw [coherentNerveMap_vertex] at h
  have r := (relativeHom_covariantModelIso (kanTerminalObject K)).precomp
    ((SSet.uliftFunctor.{u + 2, u + 1}).map kanTerminalInfinity)
  have t := ((kanTerminalHomInfinityComparisonIso K).ulift.{u + 1, u + 2}).postcomp
    Compact.spaceUniverseDiagram
  simpa only [Functor.map_comp, Category.assoc] using h ≪≫ r ≪≫ t

/-- 非可算正則 μ に関して μ-small な Kan 空間は、N の元の全共変 Hom によって μ-compact。 -/
lemma smallKanObject_isKappaCompact {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) (K : KanObject.{u}) (hK : IsKappaSmall μ K.obj) :
    Compact.IsKappaCompact.{u, u + 1} μ (coherentNerveVertex K) := by
  intro I hI hFiltered D c hc
  have hh := smallKanHomInfinity_isKappaAccessibleFunctor hμ K hK I D c hc
  have hm : IsColimitCone (mapJoinCocone
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (kanInternalHomInfinity K) ≫
        Compact.spaceUniverseDiagram) (JoinCocone.ulift c)) := by
    rw [Compact.mapJoinCocone_universe_comp]
    exact Compact.spaceUniverseDiagram_map_isColimit (D ≫ kanInternalHomInfinity K)
      (mapJoinCocone (kanInternalHomInfinity K) c) hh
  exact hm.of_functorIso ((kanHom_covariantModelIso K).precomp (JoinCocone.ulift c).val).symm

end SerrePositivity.InfinityCategories.F2.Presentable
