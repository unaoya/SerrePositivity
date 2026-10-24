module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomWeightPresentationLimit
public import SerrePositivity.InfinityCategories.F2.Presentable.VertexIsoUniverseLift

/-!
概要：Ind 図式の前層実現と標的延長の実現から Hom 係数族の表現可能性を得る。
方針：二つの実現の全 Hom 極限を同じ図式上で比較する。
規約：表現可能性は全標的係数に自然な頂点同型である。
使われ方：filtered と幾何学的実現のみから局所 Kan 余極限を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：Ind 表示と延長像の実現があれば、同じ前層の全 Hom 係数は表現可能。
方針：二つの元の全 Hom 極限の頂点を一意性で比較する。
規約：指定された両余錐とその元の頂点を保持する。
使われ方：幾何学的実現での局所 Kan 存在判定。 -/
lemma indHomWeight_realization_representable (κ : Cardinal.{u})
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β)
    {E : SSet.{u}} (p : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ IndInfinity κ C)
    (cP : JoinCocone (p ≫ indInclusionPresheaf κ C)) (hcP : IsColimitCone cP)
    (cD : JoinCocone (p ≫ G)) (hcD : IsColimitCone cD) :
    Nonempty (VertexIso
      (functorVertex (homInfinityCovariant (C := (SSet.uliftFunctor.{u + 2, u + 1}).obj D)
        (ULift.up cD.vertex)))
      ((fullPresheafHomWeightFamily F₀).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm (ULift.up cP.vertex))))) := by
  obtain ⟨dP, hdP, hvP⟩ := exists_homWeight_presentation_limit F₀ _ cP hcP (p ≫ G)
    (fullPresheafHomWeightFamily_indDiagramIso κ β hβ p)
  let dD := mapJoinCone (coyonedaInfinityMap ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))
    (JoinCone.ulift.{u + 2, u + 3}
      (F1B.coconeReverseCone (JoinCocone.ulift.{u + 1, u + 2} cD)))
  have hcD' : IsColimitCone (JoinCocone.ulift.{u + 1, u + 2} cD) :=
    (isColimitCone_iff_ulift cD).mp hcD
  have hdD : IsLimitCone dD := coyonedaInfinityMap_map_isLimit _
    ((F1B.isColimitCone_iff_reverseCone _).mp hcD')
  have hvD : dD.vertex = functorVertex
      (homInfinityCovariant (C := (SSet.uliftFunctor.{u + 2, u + 1}).obj D)
        (ULift.up cD.vertex)) := by
    dsimp only [dD]
    rw [mapJoinCone_vertex, JoinCone.ulift_vertex, F1B.coconeReverseCone_vertex,
      JoinCocone.ulift_vertex, coyonedaInfinityMap_vertex]
  exact ⟨(eqToIso (congrArg HomotopyCategory.mk hvD)).symm ≪≫
    limitVertexIso dD dP hdD hdP ≪≫ eqToIso (congrArg HomotopyCategory.mk hvP)⟩

end SerrePositivity.InfinityCategories.F2.Presentable
