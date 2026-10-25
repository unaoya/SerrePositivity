module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.OperationsCompactCardinals
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCandidates

/-!
概要：同じ実 Ind 像には、元の任意の対象の恒等射が入る。
方針：元の対象の単一 compact 表示を定値射図式へ送り、像の filtered 閉性を使う。
規約：対象を compact と仮定せず、全対象上の元の恒等射図式を回収する。
使われ方：辺クラスの pushout 保存に使う恒等射二本の供給。
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

/-- 元の対象の恒等射図式は、元の強飽和生成閉包に属する。 -/
lemma identityArrow_mem_generatedEdges (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    arrowVertexEdge ((constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x) ∈
      generatedEdges edges := by
  let d := Truncated.Edge.id (X := (truncation 2).obj C) x
  have hd : IsInvertibleEdge d := by
    change IsIso (Truncated.HomotopyCategory.homMk d)
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  have he : arrowVertexEdge ((constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x) =
      d.edge := by
    rw [constantFunctorMap_vertex]
    change SSet.yonedaEquiv ((functorVertexEquiv Δ[1] C).symm
      ((functorVertexEquiv Δ[1] C) (SSet.const x))) = d.edge
    rw [Equiv.symm_apply_apply]
    exact pinchedConstant_one x
  rw [he]
  exact (stronglySaturatedClosure_stronglySaturated
    (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).1 d hd

/-- 同じ実像は、元の全対象上の恒等射図式を含む。 -/
lemma indArrowImage_identityArrow {μ : Cardinal.{u}} [Fact μ.IsRegular]
    {A : SSet.{u}} [Quasicategory A] (edges : I → C _⦋1⦌)
    (hC : HasSmallColimits C) (hCμ : IsKappaAccessible μ C)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hff : IsFullyFaithful G) (hG : IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ x : C _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ x →
      Compact.IsKappaCompact.{u, u + 1} μ
        ((constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x))
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ f →
      arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
    (x : C _⦋0⦌) :
    IndArrowImageVertex edges G ((constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x) := by
  obtain ⟨B, hB, i, hi⟩ := hCμ.2.2
  have := hB
  obtain ⟨K, hK, hμK, a, c, hv, hc⟩ := hi.presentation x
  have := hK
  have := hμK
  let L := constantFunctorMap (Δ[1] : SSet.{u + 1}) C
  let D := (SSet.uliftFunctor.{u + 1, u}).map a ≫ i
  let q := fullSubcomplexLift (IndArrowImageVertex edges G) (D ≫ L) (by
    rintro ⟨k⟩
    exact hcover _ (hcompact _ (hi.compact (a.app _ k)))
      (identityArrow_mem_generatedEdges edges _))
  have hd : IsColimitCone (mapJoinCocone L c) :=
    constantFunctorMap_preservesSmallColimits Δ[1] K D c hc
  have hm := indArrowImage_colimit_mem edges G hC hff hG q (mapJoinCocone L c) hd
  rw [Ind.mapJoinCocone_vertex, hv] at hm
  exact hm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
