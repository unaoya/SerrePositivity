module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.AccessibleSourceNormalization
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeSliceDiagram

/-!
概要：accessible 圏の元の生成表示を、入力と元の標的の双方を固定する図式へ正規化する。
方針：入力下の全表示の余錐を元の標的上の slice 図式として読む。
規約：底の全増大余錐も元の共終な表示制限と厳密に一致させる。
使われ方：固定始域内の相対交互塔の元の両成分表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：元の生成表示は、入力の下かつ元の余錐の上で全余錐として正規化できる。
方針：入力付き表示の全増大余錐の等式を保持し、元の共終な余極限性を戻す。
規約：全小余極限の存在を仮定しない。
使われ方：元の成分入力からの全射を伴う相対交互構成の表示入力。 -/
lemma exists_nativeSourceSliceNormalization_of_isKappaAccessible
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible μ C)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (hq : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (q.app (Opposite.op ⦋0⦌) v))
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (z : JoinCocone q) (hz : z.vertex = c.vertex) :
    ∃ i : I _⦋0⦌, IsKappaFiltered μ (sliceUnder (SSet.yonedaEquiv.symm i)) ∧
      ∃ P : (SSet.uliftFunctor.{u + 1, u}).obj (sliceUnder (SSet.yonedaEquiv.symm i)) ⟶
          sliceOver ((SSet.yonedaEquiv (X := sliceUnder q)).symm z),
        P ≫ sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫ sliceUnderProjection q =
          (SSet.uliftFunctor.{u + 1, u}).map
            (sliceUnderProjection (SSet.yonedaEquiv.symm i)) ≫ D ∧
        IsColimitCone (sliceDiagramCocone P) ∧
        IsColimitCone (mapJoinCocone (sliceUnderProjection q) (sliceDiagramCocone P)) := by
  obtain ⟨i, hfilter, F, hF, c', hc', hv, haug⟩ :=
    exists_nativeSourceNormalization_of_isKappaAccessible hμ hC hK q hq D c hc z hz
  have := hfilter
  let g := (SSet.uliftFunctor.{u + 1, u}).map
    (sliceUnderProjection (SSet.yonedaEquiv.symm i))
  have hg : IsRightCofinal g := Ind.isRightCofinal_ulift _
    (smallPrefix_cosliceProjection_isRightCofinal (Fact.out : μ.IsRegular)
      (isKappaSmall_of_finite (Cardinal.IsRegular.aleph0_le Fact.out) _)
      (SSet.yonedaEquiv.symm i))
  have hcbase : IsColimitCone (mapJoinCocone (sliceUnderProjection q) c') :=
    (isColimitCone_iff_of_cocone_val_eq _ _ haug).mpr
      ((Ind.isColimitCone_iff_restrict_rightCofinal g hg c).mp hc)
  subst z
  refine ⟨i, hfilter, coconeSliceDiagram c', ?_, ?_, ?_⟩
  · rw [← Category.assoc, coconeSliceDiagram_projection]
    exact hF
  · exact (isColimitCone_iff_of_cocone_val_eq _ _ (coconeSliceDiagram_uncurry c')).mpr hc'
  · apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr hcbase
    change sliceOverUncurry (coconeSliceDiagram c') ≫ sliceUnderProjection q =
      c'.val ≫ sliceUnderProjection q
    rw [coconeSliceDiagram_uncurry]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
