module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeCompactPresentationSection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniversePointCoslice
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredCosliceCofinality

/-!
概要：filtered 表示の指定段を保ち、compact な表示頂点への切断を後続段で作る。
方針：指定段の下の元の添字を使い、全表示を同じ coslice 内へ制限する。
規約：後続段は元の添字内の実際の射を持ち、比較三角形も指定始域上にある。
使われ方：元の対象上の可算交互構成の一段延長。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：compact な指定段から compact な表示頂点への構造射は、元の後続段を通して分裂する。
方針：指定段の coslice は filtered かつ元の添字へ共終なので、相対 compact 因子化を適用する。
規約：元の添字の後続射と、指定段の下での実合成三角形を同時に保持する。
使われ方：像の二本の辺を、元の圏の同じ表示遷移と整合させる。 -/
lemma filteredStage_compact_presentation_section
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I]
    {C : SSet.{u + 1}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (i : I _⦋0⦌)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up i)))
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ c.vertex) :
    let a := (SSet.yonedaEquiv (X :=
      (SSet.uliftFunctor.{u + 1, u}).obj I)).symm (ULift.up i)
    let s := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointCosliceUniverseIso.{u, u + 1} i).hom
    let F := s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a D
    let v := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone a s D c
    ∃ j : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm i)) _⦋0⦌,
      ∃ t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ D)).Edge v.vertex (F.app _ (ULift.up j)),
        Nonempty (t.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg v (ULift.up j))
          (SSet.Edge.id v.vertex)) := by
  let a := (SSet.yonedaEquiv (X :=
      (SSet.uliftFunctor.{u + 1, u}).obj I)).symm (ULift.up i)
  let s := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointCosliceUniverseIso.{u, u + 1} i).hom
  have hreg : μ.IsRegular := Fact.out
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm i)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_sliceUnder hreg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hreg.aleph0_le _) _
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered hreg.aleph0_le I
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) := by
    dsimp only [s, a]
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointCosliceUniverseIso_projection]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isRightCofinal_sliceUnderProjection_of_filtered _)
  have hsource : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv (a ≫ D)) := by
    dsimp only [a]
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hi
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeCompact_presentation_section hμ a s D c hc hs hsource hv

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
