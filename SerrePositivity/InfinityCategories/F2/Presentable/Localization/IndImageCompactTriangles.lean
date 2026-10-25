module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageEdges

/-!
概要：compact な結論辺を持つ指定三角形では、実 Ind 像の二対三則が成立する。
方針：元の強飽和閉包の二対三則を使い、compact な結論辺を同じ実像へ回収する。
規約：一般の結論辺の compact 性は仮定しないと得られず、全二対三則とは区別する。
使われ方：HTT 5.5.4.14 の共通 compact 部分三角形の最終段。
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
variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
  (edges : I → C _⦋1⦌) (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
  (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
    Compact.IsKappaCompact.{u, u + 1} μ f →
    arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
include hcover

omit [Fact μ.IsRegular] in
/-- compact な元の閉包内辺は、全 compact 閉包射の被覆で同じ実像の辺へ戻る。 -/
lemma indArrowImageEdges_mem_of_compact_generated (e : C _⦋1⦌)
    (he : Compact.IsKappaCompact.{u, u + 1} μ (functorVertex (SSet.yonedaEquiv.symm e)))
    (hs : e ∈ generatedEdges edges) : e ∈ indArrowImageEdges edges G := by
  apply hcover _ he
  change SSet.yonedaEquiv (SSet.yonedaEquiv.symm e) ∈ generatedEdges edges
  rwa [Equiv.apply_symm_apply]

variable {x y z : C _⦋0⦌}
  {f : Truncated.Edge (X := (truncation 2).obj C) x y}
  {g : Truncated.Edge (X := (truncation 2).obj C) y z}
  {h : Truncated.Edge (X := (truncation 2).obj C) x z}

omit [Fact μ.IsRegular] in
/-- 二辺が実像に属し、合成辺が compact なら、その同じ合成辺も実像に属する。 -/
lemma indArrowImageEdges_comp_of_compact (t : f.CompStruct g h)
    (hf : f.edge ∈ indArrowImageEdges edges G) (hg : g.edge ∈ indArrowImageEdges edges G)
    (hh : Compact.IsKappaCompact.{u, u + 1} μ (functorVertex (SSet.yonedaEquiv.symm h.edge))) :
    h.edge ∈ indArrowImageEdges edges G := by
  apply indArrowImageEdges_mem_of_compact_generated edges G hcover _ hh
  exact (stronglySaturatedClosure_stronglySaturated
    (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.2.1 t
      (indArrowImageEdges_subset_generatedEdges edges G hf)
      (indArrowImageEdges_subset_generatedEdges edges G hg)

omit [Fact μ.IsRegular] in
/-- 最初の辺と合成辺が実像に属し、最後の辺が compact なら、同じ最後の辺も属する。 -/
lemma indArrowImageEdges_cancel_left_of_compact (t : f.CompStruct g h)
    (hf : f.edge ∈ indArrowImageEdges edges G) (hh : h.edge ∈ indArrowImageEdges edges G)
    (hg : Compact.IsKappaCompact.{u, u + 1} μ (functorVertex (SSet.yonedaEquiv.symm g.edge))) :
    g.edge ∈ indArrowImageEdges edges G := by
  apply indArrowImageEdges_mem_of_compact_generated edges G hcover _ hg
  exact (stronglySaturatedClosure_stronglySaturated
    (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.2.2.1 t
      (indArrowImageEdges_subset_generatedEdges edges G hf)
      (indArrowImageEdges_subset_generatedEdges edges G hh)

omit [Fact μ.IsRegular] in
/-- 最後の辺と合成辺が実像に属し、最初の辺が compact なら、同じ最初の辺も属する。 -/
lemma indArrowImageEdges_cancel_right_of_compact (t : f.CompStruct g h)
    (hg : g.edge ∈ indArrowImageEdges edges G) (hh : h.edge ∈ indArrowImageEdges edges G)
    (hf : Compact.IsKappaCompact.{u, u + 1} μ (functorVertex (SSet.yonedaEquiv.symm f.edge))) :
    f.edge ∈ indArrowImageEdges edges G := by
  apply indArrowImageEdges_mem_of_compact_generated edges G hcover _ hf
  exact (stronglySaturatedClosure_stronglySaturated
    (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.2.2.2 t
      (indArrowImageEdges_subset_generatedEdges edges G hg)
      (indArrowImageEdges_subset_generatedEdges edges G hh)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
