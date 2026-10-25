module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCoproductColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageSpanColimits
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteColimitPreservationGeneration
public import SerrePositivity.InfinityCategories.F1.Joins.PointConeSpanIso
public import SerrePositivity.InfinityCategories.Stable.UniverseHorns

/-!
概要：実像の全有限単体集合形状の余極限と、包含による指定余錐の保存。
方針：空図式は全小余積から、点 span は標準ホーンから移し、公開の有限セル帰納を使う。
規約：有限 poset に限定せず、元の大宇宙の任意の有限全図式を保持する。
使われ方：実像の全小余極限閉性への有限工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
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

/-- 任意の元の有限全図式には、包含で元の射圏の余極限に写る同じ普遍余錐がある。 -/
lemma indArrowImage_hasPreservedFiniteColimit
    (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ indArrowImageCategory edges G) :
    Ind.HasPreservedColimit (indArrowImageInclusion edges G) D := by
  let U := indArrowImageInclusion edges G
  have hsmall := h.of_le (Fact.out : κ.IsRegular).aleph0_le
  have hX := indArrowImage_hasSmallCoproducts edges hC hsmall G hff hG hcompact hcover
  have hU := indArrowImageInclusion_preservesSmallCoproducts
    edges hC hsmall G hff hG hcompact hcover
  apply Ind.hasPreservedColimit_finite_of_empty_pointSpan U ?_ ?_ K D
  · intro T p
    let E := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete PEmpty.{u + 1}))
    have hE : IsInitial E := SSet.isInitialOfNotNonempty (by
      rintro ⟨⟨v⟩⟩
      exact (v.obj 0).as.elim)
    let e : E ≅ (⊥ : T.Subcomplex).toSSet := hE.uniqueUpToIso Subcomplex.isInitialBot
    apply (Ind.hasPreservedColimit_iff_restrict_isIso U p e.hom).mpr
    obtain ⟨c, hc⟩ := hX PEmpty.{u + 1} (e.hom ≫ p)
    exact ⟨c, hc, hU _ _ c hc⟩
  · intro p
    let e := uliftHornIso.{u, u + 1} 2 0 ≪≫ pointConeSpanIso.symm
    apply (Ind.hasPreservedColimit_iff_restrict_isIso U p e.hom).mpr
    obtain ⟨c, hc⟩ := indArrowImage_hasSpanColimit edges hC h G hff hG hcompact hcover
      (e.hom ≫ p)
    exact ⟨c, hc, indArrowImageInclusion_preservesSpanColimit edges hC h G hff hG hcompact hcover
      (e.hom ≫ p) c hc⟩

/-- 実像は、大宇宙の任意の有限単体集合形状の全余極限を持つ。 -/
lemma indArrowImage_hasFiniteColimits : HasFiniteColimits (indArrowImageCategory edges G) := by
  constructor
  intro K hK D
  obtain ⟨c, hc, _⟩ := indArrowImage_hasPreservedFiniteColimit
    edges hC h G hff hG hcompact hcover K D
  exact ⟨c, hc⟩

/-- 包含は、任意の元の有限全図式の指定全余極限余錐を保存する。 -/
lemma indArrowImageInclusion_preservesFiniteColimit
    (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ indArrowImageCategory edges G)
    (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (indArrowImageInclusion edges G) c) :=
  (indArrowImage_hasPreservedFiniteColimit
    edges hC h G hff hG hcompact hcover K D).map_isColimit c hc

/-- 実像に値を持つ任意の有限全図式の、周囲の指定余極限も同じ実像に属する。 -/
lemma indArrowImage_finite_colimit_mem
    (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ indArrowImageCategory edges G)
    (c : JoinCocone (D ≫ indArrowImageInclusion edges G)) (hc : IsColimitCone c) :
    IndArrowImageVertex edges G c.vertex := by
  obtain ⟨d, hd, hUd⟩ := indArrowImage_hasPreservedFiniteColimit
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
