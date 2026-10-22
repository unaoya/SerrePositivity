module

public import SerrePositivity.InfinityCategories.F2.Presentable.PointKanExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPartialColimitFamily
public import SerrePositivity.InfinityCategories.F2.Presentable.GeneratorEquivalence

/-!
概要：coherent な部分余極限族の μ-filtered 余極限として、元の全表示の指定頂点を回収する。
方針：族の余極限を先に作り、一点への二つの Kan 拡張の一意性と cofinal 性で頂点を比較する。
規約：元の全余錐の頂点そのものへ輸送する。部分余極限の μ-compact 性はまだ結論しない。
使われ方：κ-accessibility の濃度変更で必要な、元の対象の μ-filtered 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の κ-filtered 表示の頂点を、同じ部分余極限族の μ-filtered 余極限として厳密に得る。 -/
lemma exists_smallPartialColimitPresentation {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] {I : Type u} [PartialOrder I]
    [IsCardinalFiltered I κ] (h : IsCardinalChangeBound κ μ)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : Ind.HasSmallKappaFilteredColimits κ C)
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C}
    (c : JoinCocone D) (hc : IsColimitCone c) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (SmallFilteredPieces κ μ I)) ⟶ C)
      (β : SSet.Homotopy
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalValue) ≫ D)
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece) ≫ G)),
      IsKappaFiltered μ (nerve (SmallFilteredPieces κ μ I)) ∧
      IsLeftKanExtension
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece))
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalValue) ≫ D) G β ∧
      (∀ A : SmallFilteredPieces κ μ I, ∃ a : JoinCocone (smallFilteredPartialDiagram D A),
        IsColimitCone a ∧ a.vertex = G.app _ (ULift.up (nerveVertex A))) ∧
      ∃ d : JoinCocone G, IsColimitCone d ∧ d.vertex = c.vertex := by
  obtain ⟨G, β, hβ, hG⟩ := exists_smallPartialColimitFamily hC D
  have hμ := smallFilteredPieces_nerve_isKappaFiltered h (I := I)
  have : IsKappaFiltered κ (nerve (SmallFilteredPieces κ μ I)) :=
    isKappaFiltered_of_le h.le
  obtain ⟨d, hd⟩ := hC (nerve (SmallFilteredPieces κ μ I)) G
  let r := (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (smallFilteredTotalValue (κ := κ) (μ := μ) (I := I)))
  have hc' : IsColimitCone (c.restrict r) :=
    (smallFilteredTotal_restrict_isColimit_iff h c).mp hc
  let e := leftKan_colimitVertexIso _ β hβ (c.restrict r) hc' d hd
  have ev : VertexIso d.vertex c.vertex := by
    simpa only [JoinCocone.vertex_restrict] using e
  obtain ⟨d', hd', hv⟩ := exists_colimitCone_vertex_of_iso d hd ev
  exact ⟨G, β, hμ, hβ, hG, d', hd', hv⟩

end SerrePositivity.InfinityCategories.F2.Presentable
