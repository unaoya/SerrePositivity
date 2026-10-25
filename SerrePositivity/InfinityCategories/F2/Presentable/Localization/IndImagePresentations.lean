module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCandidates

/-!
概要：実 Ind 像の各元の射には、小さい同じ濃度の filtered な実表示がある。
方針：元の Ind 頂点の単一 Yoneda 表示を送り、最後の同型だけ余錐頂点に移す。
規約：表示の図式全体と元の指定頂点を保持し、単なる対象ごとの像とはしない。
使われ方：HTT 5.5.4.13–14 の二つの実表示の同時細分。
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
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)

/-- 実像の各頂点は、元の全包含を通る一つの小さい filtered 表示の指定頂点である。 -/
lemma indArrowImageVertex_hasPresentation (hC : HasSmallColimits C)
    (G : Ind.IndInfinity κ A ⟶ generatedArrowCategory edges)
    (hG : IsKappaAccessibleFunctor κ G)
    {f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌}
    (hf : IndArrowImageVertex edges G f) :
    ∃ (K : SSet.{u}) (_hK : Quasicategory K) (_hκ : IsKappaFiltered κ K)
      (b : K ⟶ A)
      (c : JoinCocone (((SSet.uliftFunctor.{u + 1, u}).map b ≫ Ind.indYoneda κ A ≫ G) ≫
        generatedArrowInclusion edges)), c.vertex = f ∧ IsColimitCone c := by
  obtain ⟨a, ⟨ha⟩⟩ := hf
  obtain ⟨K, hK, hκ, b, c, hv, hc⟩ := indYoneda_generatorPresentation κ A a
  have := hK
  have := hκ
  let H := G ≫ generatedArrowInclusion edges
  have hp : IsKappaAccessibleFunctor κ H := hG.comp
    ((generatedArrowInclusion_preservesSmallColimits hC edges).isKappaAccessibleFunctor κ)
  have hd := hp K _ c hc
  have he : VertexIso (mapJoinCocone H c).vertex f :=
    eqToIso (congrArg HomotopyCategory.mk ((Ind.mapJoinCocone_vertex H c).trans
      (congrArg (H.app _) hv))) ≪≫ ha
  obtain ⟨d, hd, hvd⟩ := exists_colimitCone_vertex_of_iso (mapJoinCocone H c) hd he
  exact ⟨K, hK, hκ, b, d, hvd, hd⟩

/-- 周囲で compact な Yoneda 像を持つ実像の表示は、元の全項も周囲で compact。 -/
lemma indArrowImageVertex_hasCompactPresentation (hC : HasSmallColimits C)
    (G : Ind.IndInfinity κ A ⟶ generatedArrowCategory edges)
    (hG : IsKappaAccessibleFunctor κ G)
    (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} κ
      ((Ind.indYoneda κ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    {f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌}
    (hf : IndArrowImageVertex edges G f) :
    ∃ (K : SSet.{u}) (_hK : Quasicategory K) (_hκ : IsKappaFiltered κ K)
      (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ generatedArrowCategory edges)
      (c : JoinCocone (D ≫ generatedArrowInclusion edges)),
      c.vertex = f ∧ IsColimitCone c ∧
      ∀ k, Compact.IsKappaCompact.{u, u + 1} κ
        ((D ≫ generatedArrowInclusion edges).app _ k) := by
  obtain ⟨K, hK, hκ, b, c, hv, hc⟩ := indArrowImageVertex_hasPresentation edges hC G hG hf
  refine ⟨K, hK, hκ, (SSet.uliftFunctor.{u + 1, u}).map b ≫ Ind.indYoneda κ A ≫ G,
    c, hv, hc, ?_⟩
  rintro ⟨k⟩
  exact hcompact (b.app _ k)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
