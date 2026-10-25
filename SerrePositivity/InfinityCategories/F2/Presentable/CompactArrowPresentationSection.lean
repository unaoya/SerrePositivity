module

public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceCompactness
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactFactorizationTriangle

/-!
概要：compact な両端を持つ射の filtered 表示は、一段に固定始域上の切断を持つ。
方針：射を元の coslice 内で compact と判定し、その恒等辺を全三角形ごと因子化する。
規約：元の表示脚と固定始域上の二単体を保持する。
使われ方：元の対象上の可算交互構成における、途中の表示段を保つ延長。
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

/-- 概要：compact な両端の元の射は、固定始域上の表示の一段の retract になる。
方針：coslice 内の恒等辺を compact 因子化し、元の余錐脚との合成三角形を返す。
規約：三角形は元の coslice 内の実二単体で、元の圏内の実三単体を含む。
使われ方：交互列の新しい辺と、既存の表示段からの辺の整合を同時に作る。 -/
lemma compactArrow_presentation_section
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] {x y : C _⦋0⦌} (f : C.Edge x y)
    (hx : Compact.IsKappaCompact.{u, u + 1} μ x)
    (hy : Compact.IsKappaCompact.{u, u + 1} μ y)
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered μ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceUnder (SSet.yonedaEquiv.symm x))
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hv : c.vertex = edgeCosliceVertex f.toTruncated) :
    ∃ j : K _⦋0⦌,
      ∃ s : (sliceUnder (SSet.yonedaEquiv.symm x)).Edge c.vertex (D.app _ (ULift.up j)),
        Nonempty (s.CompStruct (Compact.coconeTransportLeg c (ULift.up j))
          (SSet.Edge.id c.vertex)) := by
  have hcompact : Compact.IsKappaCompact.{u, u + 1} μ c.vertex := by
    rw [hv]
    exact isKappaCompact_edgeCosliceVertex hμ f hx hy
  exact Localization.compactSource_factorization_triangle hcompact D c hc (SSet.Edge.id c.vertex)

end SerrePositivity.InfinityCategories.F2.Presentable
