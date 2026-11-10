module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceColimitCones

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.F1B.Equivalences.QCatEquivalenceOpposite
public import SerrePositivity.InfinityCategories.Core.ColimitDiagramIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：同値による元の指定余錐の保存・反映と、小さい κ-filtered 余極限の輸送。
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
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.InfinityCategories.F2 _root_.SerrePositivity.InfinityCategories.F2.Presentable

/-- 同値は宇宙 u の元の小さい κ-filtered 全余錐を保存する。 -/
lemma equivalence_preservesSmallKappaFilteredColimits (κ : Cardinal.{u})
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    {G : C ⟶ E} (hG : IsQCatEquivalence G) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G := by
  intro I hI hκ D c hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff hG c).mp hc

/-- 同じ小さい κ-filtered 余極限の存在は、元の同値で輸送される。 -/
lemma hasSmallKappaFilteredColimits_of_equivalence {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E] (e : QCatEquivalence C E)
    (hC : Ind.HasSmallKappaFilteredColimits κ C) : Ind.HasSmallKappaFilteredColimits κ E := by
  intro I hI hκ D
  obtain ⟨c, hc⟩ := hC I (D ≫ e.inv)
  have he : FunctorIso ((D ≫ e.inv) ≫ e.hom) D := by
    simpa only [Category.assoc, Category.comp_id] using e.invHomIso.precomp D
  exact (hasColimit_iff_of_functorIso he).mp
    ⟨mapJoinCocone e.hom c, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff e.isQCatEquivalence c).mp hc⟩

end SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories
