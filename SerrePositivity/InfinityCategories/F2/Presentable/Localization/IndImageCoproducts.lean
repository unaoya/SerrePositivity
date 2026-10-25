module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCompactCoproducts

/-!
概要：実 Ind 像は、元の射圏内の任意の小さい余積で閉じている。
方針：P-10 の共通表示を使い、全 compact 行の余積を実像に回収する。
規約：元の指定全余錐の頂点を結論し、添字族の μ-small 性を要求しない。
使われ方：HTT 5.5.4.14 の実像の強飽和性への余積工程。
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

/-- 元の任意の小さい離散図式の指定余極限は、実 Ind 像に属する。 -/
lemma indArrowImage_coproduct_colimit_mem
    (edges : I → C _⦋1⦌) (hC : HasSmallColimits C)
    (hbound : IsCardinalChangeBound Cardinal.aleph0 μ)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hff : IsFullyFaithful G) (hG : IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ f →
      arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
    {B : Type u}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶
      indArrowImageCategory edges G)
    (c : JoinCocone (D ≫ indArrowImageInclusion edges G)) (hc : IsColimitCone c) :
    IndArrowImageVertex edges G c.vertex := by
  apply indArrowImage_coproduct_colimit_mem_of_compactRows edges hC G hff hG hcompact
    (B := B) ?_ D c hc
  intro q cq hcq hqc hqs
  exact indArrowImage_compactCoproduct_colimit_mem edges hC hbound G hff hG hcover
    q hqc hqs cq hcq

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
