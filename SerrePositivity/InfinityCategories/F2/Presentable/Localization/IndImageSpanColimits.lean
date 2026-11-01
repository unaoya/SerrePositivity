module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageFiniteColimits
public import SerrePositivity.InfinityCategories.Simplicial.FiniteSpanNerveIso

/-!
概要：有限 poset の閉性を、元の標準 span ホーンの余極限へ移す。
方針：小宇宙の厳密な形状同型を持ち上げ、指定全余錐を制限して比較する。
規約：元の標準 span とその指定余錐を保持する。
使われ方：HTT 5.5.4.14 の Ind 像の pushout 形状の余極限閉性。
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
    HomotopyLimits.arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
include hC h hff hG hcompact hcover

/-- 実像に値を持つ元の標準 span の指定余極限は、同じ実像に入る。 -/
lemma indArrowImage_span_colimit_mem
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (horn 2 0 : SSet.{u}) ⟶
      indArrowImageCategory edges G)
    (c : JoinCocone (D ≫ indArrowImageInclusion edges G)) (hc : IsColimitCone c) :
    IndArrowImageVertex edges G c.vertex := by
  let e := (SSet.uliftFunctor.{u + 1, u}).mapIso finiteSpanNerveIso.{u}
  have hcr := (Ind.isColimitCone_iff_restrict_of_precompositionEquivalence e.hom
    (isPrecompositionEquivalence_of_iso e) c).mp hc
  have hm := indArrowImage_finitePoset_colimit_mem_of_image edges hC h G hff hG hcompact hcover
    FiniteSpanIndex (e.hom ≫ D) (c.restrict e.hom) hcr
  rwa [JoinCocone.vertex_restrict] at hm

/-- 実像は、元の標準 span 全図式の余極限を実際に持つ。 -/
lemma indArrowImage_hasSpanColimit
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (horn 2 0 : SSet.{u}) ⟶
      indArrowImageCategory edges G) : HasColimit D := by
  obtain ⟨c, hc⟩ := functor_hasSmallColimits (Δ[1] : SSet.{u + 1}) hC (horn 2 0)
    (D ≫ indArrowImageInclusion edges G)
  have hm := indArrowImage_span_colimit_mem edges hC h G hff hG hcompact hcover D c hc
  exact ⟨Ind.fullCoconeLift (IndArrowImageVertex edges G) D c hm,
    Ind.fullCoconeLift_isColimit (IndArrowImageVertex edges G) D c hm hc⟩

/-- 実像の包含は、元の標準 span の指定全余極限余錐を保存する。 -/
lemma indArrowImageInclusion_preservesSpanColimit
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (horn 2 0 : SSet.{u}) ⟶
      indArrowImageCategory edges G)
    (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (indArrowImageInclusion edges G) c) := by
  let e := (SSet.uliftFunctor.{u + 1, u}).mapIso finiteSpanNerveIso.{u}
  apply (Ind.mapJoinCocone_isColimit_iff_restrict (indArrowImageInclusion edges G) e.hom
    (isPrecompositionEquivalence_of_iso e) c).mpr
  exact indArrowImageInclusion_preservesFinitePosetColimits edges hC h G hff hG hcompact hcover
    FiniteSpanIndex (e.hom ≫ D) (c.restrict e.hom)
      ((Ind.isColimitCone_iff_restrict_of_precompositionEquivalence e.hom
        (isPrecompositionEquivalence_of_iso e) c).mp hc)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
