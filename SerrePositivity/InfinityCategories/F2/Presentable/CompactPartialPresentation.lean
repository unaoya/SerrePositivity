module

public import SerrePositivity.InfinityCategories.F2.Presentable.FilteredPartialPresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPosetColimitCompact

/-!
概要：κ-compact な全図式の指定余極限を、μ-compact な項の μ-filtered 全表示へ移す。
方針：同じ cofinal poset の小さい部分余極限族に、実証済みの compact 閉性を適用する。
規約：元の全余錐の指定頂点を厳密に保持。対象に依存しない小さい生成圏はまだ構成しない。
使われ方：accessible ∞ 圏の濃度変更における各対象の μ-compact 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の κ-compact な全表示を、同じ指定頂点の μ-compact な μ-filtered 全表示にする。 -/
lemma exists_compactPartialPresentation {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : IsCardinalChangeBound κ μ)
    {J : SSet.{u}} [Quasicategory J] [IsKappaFiltered κ J]
    {C : SSet.{u + 1}} [Quasicategory C] (hC : Ind.HasSmallKappaFilteredColimits κ C)
    {D : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ C}
    (hD : ∀ j : ((SSet.uliftFunctor.{u + 1, u}).obj J) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} κ (D.app _ j))
    (c : JoinCocone D) (hc : IsColimitCone c) :
    ∃ (K : SSet.{u}) (hK : Quasicategory K),
      letI := hK
      IsKappaFiltered μ K ∧
      ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C,
        (∀ k : K _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (G.app _ (ULift.up k))) ∧
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
    change Compact.IsKappaCompact μ (G.app _ (ULift.up (nerveVertex A)))
    rw [← hvertex]
    apply isMuCompact_smallPosetColimit_of_kappaCompact h A.val A.property.2 a ha
    intro j
    exact hD (((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (subsetInclusion A.val)) ≫ r).app _ j)
  · exact hv.trans (JoinCocone.vertex_restrict c r)

/-- κ-accessible 圏の各指定対象は、μ-compact な項の小さい μ-filtered 全表示を持つ。 -/
lemma IsKappaAccessible.exists_muCompactPresentation {κ μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible κ C)
    [Fact μ.IsRegular] (h : IsCardinalChangeBound κ μ) (x : C _⦋0⦌) :
    ∃ (K : SSet.{u}) (hK : Quasicategory K),
      letI := hK
      IsKappaFiltered μ K ∧
      ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C,
        (∀ k : K _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (G.app _ (ULift.up k))) ∧
        ∃ d : JoinCocone G, IsColimitCone d ∧ d.vertex = x := by
  have : Fact κ.IsRegular := ⟨hC.1⟩
  obtain ⟨A, hA, i, hi⟩ := hC.2.2
  have := hA
  obtain ⟨J, hJ, hκJ, a, c, hv, hc⟩ := hi.presentation x
  have := hJ
  have := hκJ
  have hD : ∀ j : ((SSet.uliftFunctor.{u + 1, u}).obj J) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} κ
        (((SSet.uliftFunctor.{u + 1, u}).map a ≫ i).app _ j) := by
    rintro ⟨j⟩
    exact hi.compact (a.app _ j)
  obtain ⟨K, hK, hμK, G, hG, d, hd, hv'⟩ :=
    exists_compactPartialPresentation h hC.2.1 hD c hc
  exact ⟨K, hK, hμK, G, hG, d, hd, hv'.trans hv⟩

end SerrePositivity.InfinityCategories.F2.Presentable
