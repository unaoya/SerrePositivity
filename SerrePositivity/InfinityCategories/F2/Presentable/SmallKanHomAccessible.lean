module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallKanHomNative
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.SpaceDiagramStrictification
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.F2.Ind.NativeCoconePreservationTransport
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredPosetNerve
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift

/-!
概要：μ-small な Kan 始点からの全内部 Hom 関手は、一般の小さい μ-filtered ∞ 余極限を保つ。
方針：元の全図式を同時 strict 化し、指定全余錐の保存を全自然同型と cofinal 制限で戻す。
規約：通常の添字への保存だけを結論にせず、元の一般 coherent 図式と余錐像を量化する。
使われ方：小さい空間の compact 性と前層の compact 生成圏。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 任意の通常の μ-filtered 添字上の元の coherent 図式の、同じ全余錐像を保存する。 -/
lemma smallKanHomInfinity_preserves_nerveCocone {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) (K : KanObject.{u}) (hK : IsKappaSmall μ K.obj)
    {J : Type u} [SmallCategory J] [IsCardinalFiltered J μ]
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ SpaceInfinity.{u})
    (c : JoinCocone G) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (kanInternalHomInfinity K) c) := by
  have := isFiltered_of_isCardinalFiltered J μ
  let F := spaceDiagramStrictification G
  let d := filteredKanColimitOrdinaryCocone F
  have hd : IsColimit (kanObjectForget.mapCocone d) := colimit.isColimit _
  have he : FunctorIso (strictCoherentDiagram F) G := by
    rw [strictCoherentDiagram_eq_kanDiagram]
    exact spaceDiagramStrictificationIso G
  exact Ind.mapJoinCocone_isColimit_of_functorIso (kanInternalHomInfinity K) he
    (strictNativeCocone d) c (Ind.strictNativeCocone_isColimit_of_filtered_forget d hd) hc
    (smallKanHomInfinity_preserves_strictCocone hμ K hK d hd)

/-- 元の空間 ∞ 圏の全内部 Hom は、任意の小さい μ-filtered ∞ 添字で余極限を保つ。 -/
lemma smallKanHomInfinity_isKappaAccessibleFunctor {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) (K : KanObject.{u}) (hK : IsKappaSmall μ K.obj) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (kanInternalHomInfinity K) := by
  intro B hB hμB G c hc
  obtain ⟨J, o, f, hJ, _, hf⟩ := Ind.exists_cofinal_kappaFiltered_poset (κ := μ) B
  let := o
  have := hJ
  let r := (SSet.uliftFunctor.{u + 1, u}).map f
  have hr : IsRightCofinal r := Ind.isRightCofinal_ulift f hf
  have hc' := (Ind.isColimitCone_iff_restrict_rightCofinal r hr c).mp hc
  have h := smallKanHomInfinity_preserves_nerveCocone hμ K hK (r ≫ G) (c.restrict r) hc'
  apply (Ind.isColimitCone_iff_restrict_rightCofinal r hr
    (mapJoinCocone (kanInternalHomInfinity K) c)).mpr
  exact (isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _)).mp h

end SerrePositivity.InfinityCategories.F2.Presentable
