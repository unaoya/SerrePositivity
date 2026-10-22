module

public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanDensityImage

/-!
概要：左 Kan 延長は、元の指定前層の元の全密度余錐をそのまま余極限へ写す。
方針：密度頂点から回収した前層が元の前層に厳密に等しいことを使う。
規約：元の前層と元の全余錐を保持。使われ方：right 分類値の元の全空間による密度表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {D : SSet.{u + 1}} [Quasicategory D]

/-- 同じ元の前層の指定全密度余錐の像は、元の左 Kan 延長によって余極限となる。 -/
lemma indLeftKanExtension_originalDensity_image_isColimit
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (hF : IsIndVertex κ C (functorVertex F)) :
    IsColimitCone (mapJoinCocone G (indDensityCocone κ F hF)) := by
  let v := (indDensityCocone κ F hF).vertex
  have hv : indVertexPresheaf κ v = F := by
    apply (presheafInfinityObjectEquiv C).injective
    change functorVertex (indVertexPresheaf κ v) = functorVertex F
    exact (indVertexPresheaf_vertex κ v).trans (indDensityCocone_vertex κ F hF)
  have hc := indLeftKanExtension_density_image_isColimit κ β hβ v
  unfold indVertexDensityCocone at hc
  have ht : ∀ (P : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}),
      indVertexPresheaf κ v = P → ∀ hP : IsIndVertex κ C (functorVertex P),
        IsColimitCone (mapJoinCocone G (indDensityCocone κ P hP)) := by
    intro P he hP
    subst P
    exact hc
  exact ht F hv hF

end SerrePositivity.InfinityCategories.F2.Ind
