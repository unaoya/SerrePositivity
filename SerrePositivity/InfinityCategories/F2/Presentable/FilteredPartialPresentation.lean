module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPartialColimitPresentation

/-!
概要：任意の小さい κ-filtered 全表示を、μ-small κ-filtered 部分余極限の μ-filtered 表示にする。
方針：F1 の同じ cofinal poset に制限し、構成済みの部分余極限族を元の図式へ戻す。
規約：元の全図式への射と全余錐を保持。頂点の回収は厳密な等式。
使われ方：濃度変更の μ-compact 性と小さい生成圏の構成への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の図式の μ-small κ-filtered な制限の全余極限を、指定頂点そのもので持つこと。 -/
def HasSmallFilteredPartialColimit (κ μ : Cardinal.{u}) {J : SSet.{u}} {C : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ C) (x : C _⦋0⦌) : Prop :=
  ∃ (K : SSet.{u}) (hK : Quasicategory K),
    letI := hK
    IsKappaFiltered κ K ∧ IsKappaSmall μ K ∧
    ∃ a : K ⟶ J, ∃ c : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a ≫ D),
      IsColimitCone c ∧ c.vertex = x

/-- 元の任意の κ-filtered 全表示を、同じ元の図式の小さい部分余極限の μ-filtered 表示へ移す。 -/
lemma exists_filteredPartialPresentation {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : IsCardinalChangeBound κ μ)
    {J : SSet.{u}} [Quasicategory J] [IsKappaFiltered κ J]
    {C : SSet.{u + 1}} [Quasicategory C] (hC : Ind.HasSmallKappaFilteredColimits κ C)
    {D : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ C}
    (c : JoinCocone D) (hc : IsColimitCone c) :
    ∃ (K : SSet.{u}) (hK : Quasicategory K),
      letI := hK
      IsKappaFiltered μ K ∧
      ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C,
        (∀ k : K _⦋0⦌, HasSmallFilteredPartialColimit κ μ D (G.app _ (ULift.up k))) ∧
        ∃ d : JoinCocone G, IsColimitCone d ∧ d.vertex = c.vertex := by
  obtain ⟨I, o, f, hI, _, hf⟩ := Ind.exists_cofinal_kappaFiltered_poset (κ := κ) J
  let := o
  have := hI
  let r := (SSet.uliftFunctor.{u + 1, u}).map f
  have hcI : IsColimitCone (c.restrict r) :=
    (Ind.isColimitCone_iff_restrict_rightCofinal r (Ind.isRightCofinal_ulift f hf) c).mp hc
  obtain ⟨G, β, hμ, _, hparts, d, hd, hv⟩ :=
    exists_smallPartialColimitPresentation h hC (c.restrict r) hcI
  refine ⟨nerve (SmallFilteredPieces κ μ I), inferInstance, hμ, G, ?_, d, hd, ?_⟩
  · intro k
    obtain ⟨A, rfl⟩ := nerveEquiv.symm.surjective k
    obtain ⟨a, ha, hvertex⟩ := hparts A
    obtain ⟨hκA, hμA⟩ := smallFilteredPiece_nerve_properties h A
    have he : smallFilteredPartialDiagram (r ≫ D) A =
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (subsetInclusion A.val) ≫ f) ≫ D := by
      dsimp only [smallFilteredPartialDiagram, r]
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    refine ⟨nerve A.val, inferInstance, hκA, hμA, nerveMap (subsetInclusion A.val) ≫ f,
      HomotopyLimits.coherentCoconeOfDiagramEq he a,
      (HomotopyLimits.coherentCoconeOfDiagramEq_isColimit_iff he a).mp ha, ?_⟩
    rw [HomotopyLimits.coherentCoconeOfDiagramEq_vertex]
    exact hvertex
  · exact hv.trans (JoinCocone.vertex_restrict c r)

end SerrePositivity.InfinityCategories.F2.Presentable
