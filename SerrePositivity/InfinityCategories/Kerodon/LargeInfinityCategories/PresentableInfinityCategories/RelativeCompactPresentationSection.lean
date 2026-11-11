module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SourceCosliceRestrictedVertex
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PointCosliceCompactVertices
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactFactorizationTriangle

/-!
概要：指定された始域からの共終な filtered 表示の中で、元の構造射の切断を一段へ因子化する。
方針：元の余錐を coslice へ制限し、その compact な頂点の恒等辺を因子化する。
規約：元の余錐と始域を固定し、coslice 内の合成二単体を返す。
使われ方：元の対象上の可算交互構成の相対一段延長。

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

/-- 概要：元の compact 構造射は、指定した始域からの表示の一段で分裂する。
方針：全余錐を元の始域の coslice 内へ移し、その恒等辺の compact 因子化を使う。
規約：同じ元の表示脚を合成辺とする実二単体を coslice 内で保持する。
使われ方：既存の表示段を保ちながら次の比較辺を選ぶ。 -/
lemma relativeCompact_presentation_section
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I A : SSet.{u}} [Quasicategory I] [Quasicategory A] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ A]
    {C : SSet.{u + 1}} [Quasicategory C]
    (a : (Δ[0] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj I)
    (s : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a))
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv (a ≫ D)))
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ c.vertex) :
    let F := s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a D
    let v := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone a s D c
    ∃ j : A _⦋0⦌,
      ∃ t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ D)).Edge v.vertex (F.app _ (ULift.up j)),
        Nonempty (t.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg v (ULift.up j))
          (SSet.Edge.id v.vertex)) := by
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone a s D c
  have hvc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone v :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone_isColimit_of_rightCofinal (Fact.out : μ.IsRegular)
      a s D c hc hs
  have hcompact : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ v.vertex := by
    dsimp only [v]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone_vertex]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_pointCosliceVertex hμ (a ≫ D) (c.restrict a) ha
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict] using hv
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSource_factorization_triangle hcompact _ v hvc
    (SSet.Edge.id v.vertex)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
