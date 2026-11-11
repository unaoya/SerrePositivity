module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageIdentities
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.InvertibleArrowIso

/-!
概要：同じ実 Ind 像を元の辺集合として読み、生成閉包への包含と全可逆辺の所属を検査。
方針：元の一次単体と全関手圏の頂点を Yoneda で厳密に往復する。
規約：強飽和性全体や生成閉包との一致をここでは主張しない。
使われ方：HTT 5.5.4.14 の辺クラスとしての強飽和条件の接続。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
  (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)

/-- 同型で飽和した実 Ind 像に属する、元の一次単体の辺クラス。 -/
def indArrowImageEdges : Set (C _⦋1⦌) :=
  {s | _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm s))}

omit [Fact μ.IsRegular] in
/-- 元の射圏頂点の像への所属と、元の同じ一次単体の辺クラスへの所属は同値。 -/
lemma indArrowImageEdges_arrowVertex_iff (f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ indArrowImageEdges edges G ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G f := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f)) = f := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] C) (SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] C).symm f))) = f
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm _)) ↔ _
  rw [he]

omit [Fact μ.IsRegular] in
/-- 実像の元の辺クラスは、元の強飽和生成閉包に含まれる。 -/
lemma indArrowImageEdges_subset_generatedEdges :
    indArrowImageEdges edges G ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges := by
  intro s hs
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageVertex_mem edges G hs
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] C).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] C) (SSet.yonedaEquiv.symm s))) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges at hm
  simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] using hm

omit [Fact μ.IsRegular] in
/-- 全恒等射を含む同じ実像の辺クラスは、元の全可逆辺を含む。 -/
lemma indArrowImageEdges_mem_of_isInvertible
    (hids : ∀ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x))
    {x y : C _⦋0⦌} (e : Truncated.Edge (X := (truncation 2).obj C) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) : e.edge ∈ indArrowImageEdges edges G := by
  let F : (Δ[1] : SSet.{u + 1}) ⟶ C := SSet.yonedaEquiv.symm e.edge
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv F)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (SSet.yonedaEquiv.apply_symm_apply e.edge)).mpr he
  let η := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.invertibleArrow_sourceIdentityIso F hF
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageVertex_iff_vertexIso edges G η).mp
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex] using hids (F.app _ (stdSimplex.obj₀Equiv.symm 0))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
