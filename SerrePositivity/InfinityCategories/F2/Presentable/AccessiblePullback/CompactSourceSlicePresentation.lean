module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.AccessibleSourceSliceNormalization

/-!
概要：accessible 圏の小さい compact 入力図式の元の余錐を、入力と標的を固定する compact 表示で表す。
方針：元の compact 生成表示を選び、その同じ表示を入力付き全表示へ正規化する。
規約：入力図式の余極限や元の圏の全小余極限を要求しない。
使われ方：相対交互構成の元の両成分の表示入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：小さい compact 入力図式の各余錐には入力と標的を固定する compact 全表示がある。
方針：元の生成表示を同じ全余錐の入力付き正規化へ渡す。
規約：元の全増大図式を保持し、全小余極限の存在を仮定しない。
使われ方：元の両成分入力からの射を伴う相対交互塔の表示。 -/
lemma exists_compactSourceSlicePresentation_of_isKappaAccessible
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible μ C)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (hq : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (q.app (Opposite.op ⦋0⦌) v))
    (z : JoinCocone q) :
    ∃ (J : SSet.{u}) (hJ : Quasicategory J), letI := hJ
      IsKappaFiltered μ J ∧
      ∃ P : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶
          sliceOver ((SSet.yonedaEquiv (X := sliceUnder q)).symm z),
        (∀ v : J _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
          ((P ≫ sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫
            sliceUnderProjection q).app (Opposite.op ⦋0⦌) (ULift.up v))) ∧
        IsColimitCone (sliceDiagramCocone P) ∧
        IsColimitCone (mapJoinCocone (sliceUnderProjection q) (sliceDiagramCocone P)) := by
  obtain ⟨A, hA, j, hj⟩ := hC.2.2
  have := hA
  obtain ⟨I, hI, hfiltered, b, c, hv, hc⟩ := hj.presentation z.vertex
  have := hI
  have := hfiltered
  let D := (SSet.uliftFunctor.{u + 1, u}).map b ≫ j
  obtain ⟨i, hfilter, P, hP, hcol, hbase⟩ :=
    exists_nativeSourceSliceNormalization_of_isKappaAccessible hμ hC hK q hq D c hc z hv.symm
  have := hfilter
  refine ⟨sliceUnder (SSet.yonedaEquiv.symm i), inferInstance, hfilter, P, ?_, hcol, hbase⟩
  intro v
  rw [hP]
  exact hj.compact (b.app (Opposite.op ⦋0⦌)
    ((sliceUnderProjection (SSet.yonedaEquiv.symm i)).app (Opposite.op ⦋0⦌) v))

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
