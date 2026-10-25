module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageSmallColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactIndCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.EndpointCompactCardinals

/-!
概要：全生成射と全 compact 閉包内射を含む presentable な実 Ind 像が実際に存在する。
方針：共通濃度と元の compact 小模型の実比較を選び、公開 P-11 による小余完備性を合わせる。
規約：強飽和生成閉包全体との一致は未証明。新しい存在仮定を入力に追加しない。
使われ方：HTT 5.5.4.14 の実像と全生成閉包を同定する残りの工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 元の presentable 圏と小さい生成族から、保存包含を持つ presentable な実像を選べる。 -/
lemma exists_compactCoveringPresentableIndImage (hC : IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ (κ μ : Cardinal.{u}) (_ : κ.IsRegular) (hμ : μ.IsRegular),
      letI : Fact μ.IsRegular := ⟨hμ⟩
      σ < μ ∧ IsCardinalChangeBound κ μ ∧ IsKappaAccessible μ C ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges,
          IsFullyFaithful G ∧ IsKappaAccessibleFunctor μ G ∧
          (∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
            ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a))) ∧
          (∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
            Compact.IsKappaCompact.{u, u + 1} μ f →
            arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f) ∧
          IsPresentable (indArrowImageCategory edges G) ∧
          PreservesSmallColimits (indArrowImageInclusion edges G) ∧
          ∀ j : I, IndArrowImageVertex edges G (generatorArrowVertex edges j) := by
  obtain ⟨κ, μ, hκ, hμ, hσ, hb, hCμ, hArμ, hgen, _⟩ :=
    exists_endpointCompactArrowCardinal hC edges σ
  have : Fact κ.IsRegular := ⟨hκ⟩
  have : Fact μ.IsRegular := ⟨hμ⟩
  obtain ⟨A, hA, G, hff, hG, hcompact, hcover⟩ :=
    exists_ambientCompactIndComparison hC.hasSmallColimits hArμ edges
  have := hA
  have hmem (f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌)
      (hf : Compact.IsKappaCompact.{u, u + 1} μ f)
      (hs : arrowVertexEdge f ∈ generatedEdges edges) : IndArrowImageVertex edges G f := by
    exact hcover (compactGeneratedArrowVertex μ edges f hf hs)
  refine ⟨κ, μ, hκ, hμ, hσ, hb, hCμ, A, hA, G, hff, hG, hcompact, hmem,
    indArrowImage_isPresentable edges hC.hasSmallColimits hb G hff hG hcompact hmem,
    indArrowImageInclusion_preservesSmallColimits
      edges hC.hasSmallColimits hb G hff hG hcompact hmem, ?_⟩
  intro j
  apply hmem _ (hgen j)
  rw [generatorArrowVertex_edge]
  exact subset_stronglySaturatedClosure _ _ (Set.mem_range_self j)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
