module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageFinitePosetColimits

/-!
概要：元の実像に値を持つ有限 poset 全図式の余極限を、同じ実像の中に構成する。
方針：像への全同値の逆で図式全体を持ち上げ、全自然同型で指定余錐を戻す。
規約：元の全図式と全余錐の普遍性を保持し、頂点ごとの持ち上げでは済ませない。
使われ方：HTT 5.5.4.14 の Ind 像の有限形状の余極限閉性。
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
  (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (h : IsCardinalChangeBound κ μ)
  (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
  (hff : IsFullyFaithful G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
  (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
    ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
  (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
    Compact.IsKappaCompact.{u, u + 1} μ f →
    HomotopyLimits.arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
include hC h hff hG hcompact hcover

/-- 実像内の有限 poset 全図式の、元の射圏での任意の指定余極限も同じ実像に入る。 -/
lemma indArrowImage_finitePoset_colimit_mem_of_image
    (P : Type u) [PartialOrder P] [Finite P]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ indArrowImageCategory edges G)
    (c : JoinCocone (D ≫ indArrowImageInclusion edges G)) (hc : IsColimitCone c) :
    IndArrowImageVertex edges G c.vertex := by
  let e := (indArrowImageFactor_isQCatEquivalence edges G hff).choose
  let H := G ≫ generatedArrowInclusion edges
  let L := D ≫ e.inv
  have he : FunctorIso (L ≫ H) (D ≫ indArrowImageInclusion edges G) := by
    rw [show H = e.hom ≫ indArrowImageInclusion edges G from
      (indArrowImageFactor_inclusion edges G).symm]
    simpa only [L, Category.assoc, Category.id_comp] using
      (e.invHomIso.precomp D).postcomp (indArrowImageInclusion edges G)
  obtain ⟨d, hd, hv⟩ := exists_colimitCocone_functorIso_sameVertex he.symm c hc
  have hm := indArrowImage_finitePoset_colimit_mem edges hC h G hff hG hcompact hcover
    P L d hd
  rwa [hv] at hm

/-- 実像は、同じ有限 poset の全図式の余極限を実際に持つ。 -/
lemma indArrowImage_hasFinitePosetColimits
    (P : Type u) [PartialOrder P] [Finite P]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ indArrowImageCategory edges G) :
    HasColimit D := by
  obtain ⟨c, hc⟩ := functor_hasSmallColimits (Δ[1] : SSet.{u + 1}) hC (nerve P)
    (D ≫ indArrowImageInclusion edges G)
  have hm := indArrowImage_finitePoset_colimit_mem_of_image edges hC h G hff hG hcompact hcover
    P D c hc
  exact ⟨Ind.fullCoconeLift (IndArrowImageVertex edges G) D c hm,
    Ind.fullCoconeLift_isColimit (IndArrowImageVertex edges G) D c hm hc⟩

/-- 実像の包含は、同じ有限 poset の元の全余極限余錐を保存する。 -/
lemma indArrowImageInclusion_preservesFinitePosetColimits
    (P : Type u) [PartialOrder P] [Finite P]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ indArrowImageCategory edges G)
    (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (indArrowImageInclusion edges G) c) := by
  obtain ⟨c₀, hc₀⟩ := functor_hasSmallColimits (Δ[1] : SSet.{u + 1}) hC (nerve P)
    (D ≫ indArrowImageInclusion edges G)
  have hm := indArrowImage_finitePoset_colimit_mem_of_image edges hC h G hff hG hcompact hcover
    P D c₀ hc₀
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
