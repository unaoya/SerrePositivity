module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceColimitCones

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.QCatEquivalenceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitDiagramIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の小さい κ-filtered 余極限の存在と保存性を同値に沿って輸送する。
方針：同じ反転錐の既存の極限保存を使い、逆関手と全自然同型で存在を輸送する。
規約：元の全余錐を保持。図式の小ささや濃度の宇宙を変更しない。
使われ方：accessible 圏の同値不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories
open _root_.SerrePositivity.InfinityCategories

/-- 同値は宇宙 u の元の小さい κ-filtered 全余錐を保存する。 -/
lemma equivalence_preservesSmallKappaFilteredColimits (κ : Cardinal.{u})
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    {G : C ⟶ E} (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence G) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G := by
  intro I hI hκ D c hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff hG c).mp hc

/-- 同じ小さい κ-filtered 余極限の存在は、元の同値で輸送される。 -/
lemma hasSmallKappaFilteredColimits_of_equivalence {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E)
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ E := by
  intro I hI hκ D
  obtain ⟨c, hc⟩ := hC I (D ≫ e.inv)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((D ≫ e.inv) ≫ e.hom) D := by
    simpa only [Category.assoc, Category.comp_id] using e.invHomIso.precomp D
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_functorIso he).mp
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone e.hom c, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff e.isQCatEquivalence c).mp hc⟩

end SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories
