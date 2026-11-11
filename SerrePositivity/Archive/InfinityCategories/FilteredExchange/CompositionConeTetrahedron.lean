module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConeTetrahedronParameter
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CompositionAppendDiagram
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RightSliceAppendFront
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionTriangle

/-!
概要：元の実合成三角形へ指定終点を追加し、元の 012 面を厳密に保持する。
方針：元の三角形の実全錐と、同じ追加族の全面回収を使う。
規約：元の全 Hom 係数と指定射を保持。使われ方：Ncomp の四面の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実三角形へ指定射を追加した、同じ二 Hom 全係数の実四面体族。 -/
def coherentCompositionConeTetrahedron
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z W : C) (g : Z ⟶ W) :
    Δ[3] ⊗ ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)) ⟶ SimplicialNerve C :=
  coneTetrahedronParameter _ ≫ coherentCompositionAppendDiagram X Y Z W g

/-- 同じ実四面体の 012 面は、元の全係数付き coherent 合成三角形そのもの。 -/
lemma coherentCompositionConeTetrahedron_face012
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z W : C) (g : Z ⟶ W) :
    (stdSimplex.δ (3 : Fin 4) ▷ _) ≫ coherentCompositionConeTetrahedron X Y Z W g =
      coherentCompositionTriangle X Y Z := by
  rw [coherentCompositionConeTetrahedron, ← Category.assoc, coneTetrahedronParameter_front,
    Category.assoc, coherentCompositionAppendDiagram, coherentRightSliceAppendEdge_front,
    triangleRightConeParameter_comp]
  rfl

/-- 元の 012 面の厳密回収は、任意の同時係数制限でも保持される。 -/
lemma coherentCompositionConeTetrahedron_face012_precomp
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z W : C) (g : Z ⟶ W)
    {P : SSet.{max u v}}
    (q : P ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)) :
    (stdSimplex.δ (3 : Fin 4) ▷ P) ≫ (Δ[3] ◁ q) ≫
        coherentCompositionConeTetrahedron X Y Z W g =
      (Δ[2] ◁ q) ≫ coherentCompositionTriangle X Y Z := by
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    coherentCompositionConeTetrahedron_face012]

end SerrePositivity.InfinityCategories.F2
