module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPosetColimitGenerators

/-!
概要：共通の小さい部分余極限族に値が同型な、各対象の μ-filtered 全表示を構成する。
方針：元の生成図式を cofinal poset へ制限し、各小部分を同じ符号型へ移す。
規約：元の全余錐の指定頂点と、全表示の coherent な全射を保持する。
使われ方：小さい族の全部分圏への表示の移送と、濃度変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 各対象は、同じ小さい符号族の値に同型な項の μ-filtered 全表示を持つ。 -/
lemma IsKappaCompactGenerating.exists_smallFamilyPresentation
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ) {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C]
    (hC : Ind.HasSmallKappaFilteredColimits κ C)
    {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C}
    (hi : IsKappaCompactGenerating κ i) (x : C _⦋0⦌) :
    ∃ (K : SSet.{u}) (hK : Quasicategory K),
      letI := hK
      IsKappaFiltered μ K ∧
      ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C,
        (∀ k : K _⦋0⦌, ∃ q : SmallPosetDiagramCode κ μ A,
          Nonempty (VertexIso (G.app _ (ULift.up k)) (q.vertex hC i))) ∧
        ∃ d : JoinCocone G, IsColimitCone d ∧ d.vertex = x := by
  obtain ⟨J, hJ, hκJ, a, c, hv, hc⟩ := hi.presentation x
  have := hJ
  have := hκJ
  obtain ⟨I, o, f, hI, _, hf⟩ := Ind.exists_cofinal_kappaFiltered_poset (κ := κ) J
  let := o
  have := hI
  let r := (SSet.uliftFunctor.{u + 1, u}).map f
  have hcI : IsColimitCone (c.restrict r) :=
    (Ind.isColimitCone_iff_restrict_rightCofinal r (Ind.isRightCofinal_ulift f hf) c).mp hc
  obtain ⟨G, β, hμ, _, hparts, d, hd, hv'⟩ :=
    exists_smallPartialColimitPresentation h hC (c.restrict r) hcI
  refine ⟨nerve (SmallFilteredPieces κ μ I), inferInstance, hμ, G, ?_, d, hd, ?_⟩
  · intro k
    obtain ⟨B, rfl⟩ := nerveEquiv.symm.surjective k
    obtain ⟨b, hb, hvertex⟩ := hparts B
    change ∃ q : SmallPosetDiagramCode κ μ A,
      Nonempty (VertexIso (G.app _ (ULift.up (nerveVertex B))) (q.vertex hC i))
    rw [← hvertex]
    let p := nerveMap (subsetInclusion B.val) ≫ f ≫ a
    have he : smallFilteredPartialDiagram
        (r ≫ (SSet.uliftFunctor.{u + 1, u}).map a ≫ i) B =
          (SSet.uliftFunctor.{u + 1, u}).map p ≫ i := by
      dsimp only [smallFilteredPartialDiagram, r, p]
      simp only [Functor.map_comp, Category.assoc]
    have := B.property.1
    let b' := HomotopyLimits.coherentCoconeOfDiagramEq he b
    have hb' : IsColimitCone b' :=
      (HomotopyLimits.coherentCoconeOfDiagramEq_isColimit_iff he b).mp hb
    obtain ⟨q, hq⟩ := exists_smallPosetColimitGeneratorIso hC i B.val B.property.2 p b' hb'
    refine ⟨q, ?_⟩
    simpa only [b', HomotopyLimits.coherentCoconeOfDiagramEq_vertex] using hq
  · exact hv'.trans ((JoinCocone.vertex_restrict c r).trans hv)

end SerrePositivity.InfinityCategories.F2.Presentable
