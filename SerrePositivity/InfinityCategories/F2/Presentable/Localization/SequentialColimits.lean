module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageAllFiniteColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceCoproducts
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceFiniteColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.SequentialPreservedColimits

/-!
概要：Ind 実像と固定始域圏で、元の可算列の余極限を構成する。
方針：公開された望遠鏡の一般入口に、検証済みの小余積・有限余極限を渡す。
規約：全小余極限や強飽和性の完成は結論しない。
使われ方：HTT 4.4.2.6–7 の小余極限生成への可算列工程。
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
variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
  {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- Ind 実像の元の可算列には、元の射圏での余極限となる普遍余錐がある。 -/
lemma indArrowImage_hasPreservedSequentialColimit
    (edges : I → C _⦋1⦌) (hC : HasSmallColimits C) (h : IsCardinalChangeBound κ μ)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hff : IsFullyFaithful G) (hG : IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ f →
      arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
      indArrowImageCategory edges G) :
    Ind.HasPreservedColimit (indArrowImageInclusion edges G) F := by
  have hsmall := h.of_le (Fact.out : κ.IsRegular).aleph0_le
  exact hasPreservedColimit_sequential_of_coproducts_finite
    (indArrowImageInclusion edges G)
    (indArrowImage_hasSmallCoproducts edges hC hsmall G hff hG hcompact hcover)
    (indArrowImageInclusion_preservesSmallCoproducts edges hC hsmall G hff hG hcompact hcover)
    (indArrowImage_hasPreservedFiniteColimit edges hC h G hff hG hcompact hcover) F

/-- 固定始域の閉包内射の元の可算列にも、周囲で保存される普遍余錐がある。 -/
lemma generatedSource_hasPreservedSequentialColimit
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
      generatedSourceCategory edges x) :
    Ind.HasPreservedColimit (generatedSourceInclusion edges x) F :=
  hasPreservedColimit_sequential_of_coproducts_finite (generatedSourceInclusion edges x)
    (generatedSource_hasSmallCoproducts hC edges x)
    (generatedSourceInclusion_preservesSmallCoproducts hC edges x)
    (generatedSource_hasPreservedFiniteColimit hC edges x) F

/-- 固定始域の閉包内射の可算列の、元の指定余極限も同じ閉包条件を満たす。 -/
lemma generatedSource_sequential_colimit_mem
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
      generatedSourceCategory edges x)
    (c : JoinCocone (F ≫ generatedSourceInclusion edges x)) (hc : IsColimitCone c) :
    (JoinCocone.leg c.vertex (𝟙 Δ[0])).edge ∈ generatedEdges edges := by
  obtain ⟨d, hd, hUd⟩ := generatedSource_hasPreservedSequentialColimit hC edges x F
  have hm : (JoinCocone.leg
      (mapJoinCocone (generatedSourceInclusion edges x) d).vertex (𝟙 Δ[0])).edge ∈
        generatedEdges edges := by
    rw [Ind.mapJoinCocone_vertex]
    exact fullSubcomplexOnVertices_vertex d.vertex
  have hi := VertexIso.map
    (colimitConeIso (mapJoinCocone (generatedSourceInclusion edges x) d) c hUd hc)
    (sliceUnderProjection (F ≫ generatedSourceInclusion edges x))
  exact (generatedSourceCondition_iff_vertexIso edges x hi).mp hm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
