module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteSimplicialHomNative
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.SpaceDiagramStrictification
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.F2.Ind.NativeCoconePreservationTransport
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredPosetNerve
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift

/-!
概要：有限単体集合始点の全内部 Hom は、一般の小さい filtered ∞ 余極限を保つ。
方針：同じ strict 模型の保存を、元の全自然同型と cofinal 制限によって指定余錐へ戻す。
規約：添字は任意の coherent な filtered ∞ 圏。有限始点に Kan 性は要求しない。
使われ方：有限単体集合の Kan 置換の compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 任意の通常の filtered 添字上の元の coherent 図式の、同じ全余錐像を保存する。 -/
lemma finiteSimplicialHomInfinity_preserves_nerveCocone (K : SSet.{u}) [K.Finite]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ SpaceInfinity.{u})
    (c : JoinCocone G) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (simplicialInternalHomInfinity K) c) := by
  let F := spaceDiagramStrictification G
  let d := filteredKanColimitOrdinaryCocone F
  have hd : IsColimit (kanObjectForget.mapCocone d) := colimit.isColimit _
  have he : FunctorIso (strictCoherentDiagram F) G := by
    rw [strictCoherentDiagram_eq_kanDiagram]
    exact spaceDiagramStrictificationIso G
  exact Ind.mapJoinCocone_isColimit_of_functorIso (simplicialInternalHomInfinity K) he
    (strictNativeCocone d) c (Ind.strictNativeCocone_isColimit_of_filtered_forget d hd) hc
    (finiteSimplicialHomInfinity_preserves_strictCocone K d hd)

/-- 元の空間 ∞ 圏の全内部 Hom は、任意の小さい filtered ∞ 添字で余極限を保つ。 -/
lemma finiteSimplicialHomInfinity_isKappaAccessibleFunctor (K : SSet.{u}) [K.Finite] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor Cardinal.aleph0 (simplicialInternalHomInfinity K) := by
  intro B hB hμB G c hc
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  obtain ⟨J, o, f, hJ, _, hf⟩ := Ind.exists_cofinal_kappaFiltered_poset (κ := Cardinal.aleph0) B
  let := o
  have := hJ
  have := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  let r := (SSet.uliftFunctor.{u + 1, u}).map f
  have hr : IsRightCofinal r := Ind.isRightCofinal_ulift f hf
  have hc' := (Ind.isColimitCone_iff_restrict_rightCofinal r hr c).mp hc
  have h := finiteSimplicialHomInfinity_preserves_nerveCocone K (r ≫ G) (c.restrict r) hc'
  apply (Ind.isColimitCone_iff_restrict_rightCofinal r hr
    (mapJoinCocone (simplicialInternalHomInfinity K) c)).mpr
  exact (isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _)).mp h

end SerrePositivity.InfinityCategories.F2.Presentable
