module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageAllFiniteColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.FiniteCoproductColimitGeneration

/-!
概要：実 Ind 像の全小余極限の存在・保存と presentable 性を構成する。
方針：公開 P-11 に全小余積と全有限余極限を渡し、既存の accessibility と合わせる。
規約：生成閉包全体との一致と二対三則はまだ主張しない。
使われ方：HTT 5.5.4.14 の実像の全小余極限閉性。
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
  (edges : I → C _⦋1⦌) (hC : HasSmallColimits C) (h : IsCardinalChangeBound κ μ)
  (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
  (hff : IsFullyFaithful G) (hG : IsKappaAccessibleFunctor μ G)
  (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
    ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
  (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
    Compact.IsKappaCompact.{u, u + 1} μ f →
    arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
include hC h hff hG hcompact hcover

/-- 元の任意の小形状の図式に、元の射圏で保存される同じ普遍余錐が存在する。 -/
lemma indArrowImage_hasPreservedSmallColimit
    (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ indArrowImageCategory edges G) :
    Ind.HasPreservedColimit (indArrowImageInclusion edges G) D := by
  have hsmall := h.of_le (Fact.out : κ.IsRegular).aleph0_le
  exact hasPreservedColimit_of_coproducts_finite (indArrowImageInclusion edges G)
    (indArrowImage_hasSmallCoproducts edges hC hsmall G hff hG hcompact hcover)
    (indArrowImageInclusion_preservesSmallCoproducts edges hC hsmall G hff hG hcompact hcover)
    (indArrowImage_hasPreservedFiniteColimit edges hC h G hff hG hcompact hcover) K D

/-- 実 Ind 像は全ての小余極限を持つ。 -/
lemma indArrowImage_hasSmallColimits : HasSmallColimits (indArrowImageCategory edges G) := by
  intro K D
  obtain ⟨c, hc, _⟩ := indArrowImage_hasPreservedSmallColimit
    edges hC h G hff hG hcompact hcover K D
  exact ⟨c, hc⟩

/-- 実 Ind 像の包含は元の任意の小図式の指定余極限を保つ。 -/
lemma indArrowImageInclusion_preservesSmallColimits :
    PreservesSmallColimits (indArrowImageInclusion edges G) := by
  intro K D c hc
  exact (indArrowImage_hasPreservedSmallColimit
    edges hC h G hff hG hcompact hcover K D).map_isColimit c hc

/-- 元の実 Ind 像は accessible かつ小余完備、従って presentable である。 -/
lemma indArrowImage_isPresentable : IsPresentable (indArrowImageCategory edges G) :=
  ⟨(indArrowImage_isKappaAccessible edges G hff).isAccessible,
    indArrowImage_hasSmallColimits edges hC h G hff hG hcompact hcover⟩

/-- 実像に値を持つ元の任意の小図式の、周囲の指定余極限も同じ実像に属する。 -/
lemma indArrowImage_small_colimit_mem
    (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ indArrowImageCategory edges G)
    (c : JoinCocone (D ≫ indArrowImageInclusion edges G)) (hc : IsColimitCone c) :
    IndArrowImageVertex edges G c.vertex := by
  obtain ⟨d, hd, hUd⟩ := indArrowImage_hasPreservedSmallColimit
    edges hC h G hff hG hcompact hcover K D
  have hm : IndArrowImageVertex edges G
      (mapJoinCocone (indArrowImageInclusion edges G) d).vertex := by
    rw [Ind.mapJoinCocone_vertex]
    exact fullSubcomplexOnVertices_vertex d.vertex
  have hi := VertexIso.map
    (colimitConeIso (mapJoinCocone (indArrowImageInclusion edges G) d) c hUd hc)
    (sliceUnderProjection (D ≫ indArrowImageInclusion edges G))
  exact (indArrowImageVertex_iff_vertexIso edges G hi).mp hm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
