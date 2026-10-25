module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCoproducts
public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductRealizationPreservation

/-!
概要：実像内の全小余積の存在と、包含の指定余積保存を構成する。
方針：周囲の指定余積を全部分圏に持ち上げ、元の普遍余錐の一意性で保存を示す。
規約：全小余極限閉性・強飽和性はまだ主張しない。
使われ方：実像の強飽和性への余積工程。
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
variable {μ : Cardinal.{u}} [Fact μ.IsRegular]
  {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
  (edges : I → C _⦋1⦌) (hC : HasSmallColimits C) (h : IsCardinalChangeBound Cardinal.aleph0 μ)
  (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
  (hff : IsFullyFaithful G) (hG : IsKappaAccessibleFunctor μ G)
  (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
    ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
  (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
    Compact.IsKappaCompact.{u, u + 1} μ f →
    HomotopyLimits.arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
include hC h hff hG hcompact hcover

/-- 実像は、元の任意の小さい余積を実際に持つ。 -/
lemma indArrowImage_hasSmallCoproducts
    : HasSmallCoproducts (indArrowImageCategory edges G) := by
  intro B D
  obtain ⟨c, hc⟩ := functor_hasSmallColimits (Δ[1] : SSet.{u + 1}) hC (nerve (Discrete B))
    (D ≫ indArrowImageInclusion edges G)
  have hm := indArrowImage_coproduct_colimit_mem edges hC h G hff hG hcompact hcover
    D c hc
  exact ⟨Ind.fullCoconeLift (IndArrowImageVertex edges G) D c hm,
    Ind.fullCoconeLift_isColimit (IndArrowImageVertex edges G) D c hm hc⟩

/-- 実像の包含は、元の任意の小さい余積の指定全余錐を保存する。 -/
lemma indArrowImageInclusion_preservesSmallCoproducts
    : PreservesSmallCoproducts (indArrowImageInclusion edges G) := by
  intro B D c hc
  obtain ⟨c₀, hc₀⟩ := functor_hasSmallColimits (Δ[1] : SSet.{u + 1}) hC (nerve (Discrete B))
    (D ≫ indArrowImageInclusion edges G)
  have hm := indArrowImage_coproduct_colimit_mem edges hC h G hff hG hcompact hcover
    D c₀ hc₀
  let V := IndArrowImageVertex edges G
  let d := Ind.fullCoconeLift V D c₀ hm
  have hd := Ind.fullCoconeLift_isColimit V D c₀ hm hc₀
  have hi : IsColimitCone (mapJoinCocone (indArrowImageInclusion edges G) d) := by
    change IsColimitCone (mapJoinCocone (fullSubcomplexOnVertices _ V).ι
      (Ind.fullCoconeLift V D c₀ hm))
    rw [Ind.fullCoconeLift_inclusion]
    exact hc₀
  exact Ind.mapJoinCocone_isColimit_of_functorIso (indArrowImageInclusion edges G)
    (Iso.refl _) d c hd hc hi

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
