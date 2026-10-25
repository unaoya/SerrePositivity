module

public import SerrePositivity.InfinityCategories.F2.Presentable.RelativeCompactPresentationSection
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversePointCoslice
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredCosliceCofinality

/-!
概要：filtered 表示の指定段を保ち、compact な表示頂点への切断を後続段で作る。
方針：指定段の下の元の添字を使い、全表示を同じ coslice 内へ制限する。
規約：後続段は元の添字内の実際の射を持ち、比較三角形も指定始域上にある。
使われ方：元の対象上の可算交互構成の一段延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：compact な指定段から compact な表示頂点への構造射は、元の後続段を通して分裂する。
方針：指定段の coslice は filtered かつ元の添字へ共終なので、相対 compact 因子化を適用する。
規約：元の添字の後続射と、指定段の下での実合成三角形を同時に保持する。
使われ方：像の二本の辺を、元の圏の同じ表示遷移と整合させる。 -/
lemma filteredStage_compact_presentation_section
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    {C : SSet.{u + 1}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c) (i : I _⦋0⦌)
    (hi : Compact.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up i)))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ c.vertex) :
    let a := (SSet.yonedaEquiv (X :=
      (SSet.uliftFunctor.{u + 1, u}).obj I)).symm (ULift.up i)
    let s := (pointCosliceUniverseIso.{u, u + 1} i).hom
    let F := s ≫ sliceUnderPostcomp a D
    let v := sourceCosliceRestrictedCocone a s D c
    ∃ j : (sliceUnder (SSet.yonedaEquiv.symm i)) _⦋0⦌,
      ∃ t : (sliceUnder (a ≫ D)).Edge v.vertex (F.app _ (ULift.up j)),
        Nonempty (t.CompStruct (Compact.coconeTransportLeg v (ULift.up j))
          (SSet.Edge.id v.vertex)) := by
  let a := (SSet.yonedaEquiv (X :=
      (SSet.uliftFunctor.{u + 1, u}).obj I)).symm (ULift.up i)
  let s := (pointCosliceUniverseIso.{u, u + 1} i).hom
  have hreg : μ.IsRegular := Fact.out
  have : IsKappaFiltered μ (sliceUnder (SSet.yonedaEquiv.symm i)) :=
    isKappaFiltered_sliceUnder hreg (isKappaSmall_of_finite hreg.aleph0_le _) _
  have : IsFilteredInfinity I := isFilteredInfinity_of_isKappaFiltered hreg.aleph0_le I
  have hs : IsRightCofinal (s ≫ sliceUnderProjection a) := by
    dsimp only [s, a]
    rw [pointCosliceUniverseIso_projection]
    exact Ind.isRightCofinal_ulift _ (isRightCofinal_sliceUnderProjection_of_filtered _)
  have hsource : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv (a ≫ D)) := by
    dsimp only [a]
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hi
  exact relativeCompact_presentation_section hμ a s D c hc hs hsource hv

end SerrePositivity.InfinityCategories.F2.Presentable
