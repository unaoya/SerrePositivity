module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CompositionConeTetrahedron
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConeTetrahedronOtherFaces
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RightSliceAppendBack
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionPrismPost
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TriangleConeNaturality

/-!
概要：元の実四面体の 013 面は、同じ最終射で係数を後合成した元の合成三角形。
方針：追加族の実終端面と、元の合成 prism の後合成自然性を貼る。
規約：元の全係数・指定射・実全面を保持。使われ方：Ncomp の指定四面体比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実四面体の 013 面は、第二 Hom を同じ最終射で後合成した実合成三角形。 -/
lemma coherentCompositionConeTetrahedron_face013
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z W : C) (g : Z ⟶ W) :
    (stdSimplex.δ (2 : Fin 4) ▷ _) ≫ coherentCompositionConeTetrahedron X Y Z W g =
      (Δ[2] ◁ (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)) ⊗ₘ
        (SSet.uliftFunctor.{v, u}).map (eHomWhiskerLeft SSet Y g))) ≫
          coherentCompositionTriangle X Y W := by
  rw [coherentCompositionConeTetrahedron, ← Category.assoc, coneTetrahedronParameter_face013,
    ← triangleRightConeParameter_eq_simplexCone, Category.assoc,
    coherentCompositionAppendDiagram, coherentRightSliceAppendEdge_back,
    coherentCompositionPrism_post, sliceOverUncurry_precomp, ← Category.assoc,
    triangleRightConeParameter_naturality, Category.assoc, triangleRightConeParameter_comp]
  rfl

/-- 013 面の同じ指定後合成との一致は、任意の同時係数制限でも保持される。 -/
lemma coherentCompositionConeTetrahedron_face013_precomp
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z W : C) (g : Z ⟶ W)
    {P : SSet.{max u v}}
    (q : P ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)) :
    (stdSimplex.δ (2 : Fin 4) ▷ P) ≫ (Δ[3] ◁ q) ≫
        coherentCompositionConeTetrahedron X Y Z W g =
      (Δ[2] ◁ (q ≫ (𝟙 _ ⊗ₘ
        (SSet.uliftFunctor.{v, u}).map (eHomWhiskerLeft SSet Y g)))) ≫
          coherentCompositionTriangle X Y W := by
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    coherentCompositionConeTetrahedron_face013, ← whiskerLeft_comp_assoc]

end SerrePositivity.InfinityCategories.F2
