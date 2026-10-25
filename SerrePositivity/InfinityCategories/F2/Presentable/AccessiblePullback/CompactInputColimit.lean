module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CompactInputPresentation

/-!
概要：元の入力付き compact 表示内の序数図式から compact な最終成分余極限を構成する。
方針：同じ固定始域内の余極限を元の標的上へ持ち上げる。
規約：元の入力と標的を保ち、元の圏の κ₀-filtered 余極限だけを使う。
使われ方：相対交互構成の compact 成分対の最終頂点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：元の入力付き表示の序数図式は compact な成分と compact な像を持つ全余極限を持つ。
方針：固定始域内の compact 序数余極限を、同じ元の標的上へ持ち上げる。
規約：元の全図式とその底での余極限性を同時に返す。
使われ方：共通の底上で比較する compact 成分対。 -/
lemma exists_compactInputOrdinalColimit
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {K C B : SSet.{u + 1}} [Quasicategory K] [Quasicategory C] [Quasicategory B]
    (hC : Ind.HasSmallKappaFilteredColimits κ C)
    (p : C ⟶ B) (hp : IsKappaAccessibleFunctor κ p)
    (hpCompact : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app (Opposite.op ⦋0⦌) v))
    {q : K ⟶ C} {z : JoinCocone q} (N : CompactInputPresentation μ q z)
    (J : nerve κ.ord.ToType ⟶ N.index) :
    ∃ d : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map J ≫ N.diagram),
      IsColimitCone d ∧
      IsColimitCone (mapJoinCocone
        (sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫
          sliceUnderProjection q) d) ∧
      Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫
          sliceUnderProjection q).app (Opposite.op ⦋0⦌) d.vertex) ∧
      Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫
          sliceUnderProjection q ≫ p).app (Opposite.op ⦋0⦌) d.vertex) := by
  have := Cardinal.nonempty_ord_toType (c := κ) (Cardinal.IsRegular.ne_zero Fact.out)
  letI := WellFoundedLT.toOrderBot κ.ord.ToType
  let x := (SSet.yonedaEquiv (X := sliceUnder q)).symm z
  let Q := (SSet.uliftFunctor.{u + 1, u}).map J ≫ N.diagram
  let D := Q ≫ sliceOverProjection x
  have hD : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ
      ((D ≫ sliceUnderProjection q).app (Opposite.op ⦋0⦌) v) := by
    rintro ⟨v⟩
    exact N.compact (J.app (Opposite.op ⦋0⦌) v)
  have hDp : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ
      ((D ≫ sliceUnderProjection q ≫ p).app (Opposite.op ⦋0⦌) v) := by
    intro v
    exact hpCompact _ (hD v)
  obtain ⟨d₀, hd₀, hv₀, hvp₀⟩ :=
    exists_fixedSourceOrdinalColimit_compact_image h hC p hp q D hD hDp
  obtain ⟨d, hd, hproj⟩ := exists_sliceOver_colimitCone_with_projection x Q d₀ hd₀
  have hb₀ : IsColimitCone (mapJoinCocone (sliceUnderProjection q) d₀) :=
    (fixedSource_orderBot_isColimitCone_iff_projection q κ.ord.ToType D d₀).mp hd₀
  have hb : IsColimitCone (mapJoinCocone (sliceOverProjection x ≫ sliceUnderProjection q) d) := by
    apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr hb₀
    change d.val ≫ (sliceOverProjection x ≫ sliceUnderProjection q) = d₀.val ≫ sliceUnderProjection q
    rw [← Category.assoc, hproj]
  have hm : mapJoinCocone (sliceOverProjection x) d = d₀ := Subtype.ext hproj
  have hv : (sliceOverProjection x).app (Opposite.op ⦋0⦌) d.vertex = d₀.vertex := by
    simpa only [Ind.mapJoinCocone_vertex] using
      congrArg (fun c : JoinCocone D ↦ c.vertex) hm
  refine ⟨d, hd, hb, ?_, ?_⟩
  · change Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceUnderProjection q).app (Opposite.op ⦋0⦌)
        ((sliceOverProjection x).app (Opposite.op ⦋0⦌) d.vertex))
    rw [hv]
    exact hv₀
  · change Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceUnderProjection q ≫ p).app (Opposite.op ⦋0⦌)
        ((sliceOverProjection x).app (Opposite.op ⦋0⦌) d.vertex))
    rw [hv]
    exact hvp₀

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
