module

public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceRestrictedVertex
public import SerrePositivity.InfinityCategories.F2.Presentable.PointCosliceCompactVertices
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactFactorizationTriangle

/-!
概要：指定された始域からの共終な filtered 表示の中で、元の構造射の切断を一段へ因子化する。
方針：元の余錐を coslice へ制限し、その compact な頂点の恒等辺を因子化する。
規約：元の余錐と始域を固定し、coslice 内の合成二単体を返す。
使われ方：元の対象上の可算交互構成の相対一段延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の compact 構造射は、指定した始域からの表示の一段で分裂する。
方針：全余錐を元の始域の coslice 内へ移し、その恒等辺の compact 因子化を使う。
規約：同じ元の表示脚を合成辺とする実二単体を coslice 内で保持する。
使われ方：既存の表示段を保ちながら次の比較辺を選ぶ。 -/
lemma relativeCompact_presentation_section
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I A : SSet.{u}} [Quasicategory I] [Quasicategory A] [IsKappaFiltered μ A]
    {C : SSet.{u + 1}} [Quasicategory C]
    (a : (Δ[0] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj I)
    (s : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder a)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hs : IsRightCofinal (s ≫ sliceUnderProjection a))
    (ha : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv (a ≫ D)))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ c.vertex) :
    let F := s ≫ sliceUnderPostcomp a D
    let v := sourceCosliceRestrictedCocone a s D c
    ∃ j : A _⦋0⦌,
      ∃ t : (sliceUnder (a ≫ D)).Edge v.vertex (F.app _ (ULift.up j)),
        Nonempty (t.CompStruct (Compact.coconeTransportLeg v (ULift.up j))
          (SSet.Edge.id v.vertex)) := by
  let v := sourceCosliceRestrictedCocone a s D c
  have hvc : IsColimitCone v :=
    sourceCosliceRestrictedCocone_isColimit_of_rightCofinal (Fact.out : μ.IsRegular)
      a s D c hc hs
  have hcompact : Compact.IsKappaCompact.{u, u + 1} μ v.vertex := by
    dsimp only [v]
    rw [sourceCosliceRestrictedCocone_vertex]
    apply isKappaCompact_pointCosliceVertex hμ (a ≫ D) (c.restrict a) ha
    simpa only [JoinCocone.vertex_restrict] using hv
  exact Localization.compactSource_factorization_triangle hcompact _ v hvc
    (SSet.Edge.id v.vertex)

end SerrePositivity.InfinityCategories.F2.Presentable
