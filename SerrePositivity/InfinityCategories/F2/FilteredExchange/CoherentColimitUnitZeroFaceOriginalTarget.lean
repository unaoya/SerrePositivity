module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitZeroFaceOriginalSection
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePointedTarget

/-!
概要：第一辺で前合成した元の指定三角形の実終点を、元の二作用の native 合成へ揃える。
方針：全パラメータを保つ頂点制限と、同じ指定三角形の終点式を使う。
規約：元の三作用を保持。使われ方：第零面の指定全族比較の終点での表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q₀ Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (H : SSet.Homotopy F Q₀)
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)
  {a : SSet.Homotopy Q₀ Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy Q₀ Q₂}
  (S : FunctorCompositionTriangle a b c)

/-- 実第一辺の終点と、元の指定二辺の選択済み作用による全パラメータの厳密な合成。 -/
def coherentColimitUnitZeroFaceOriginalTargetMap (_S : FunctorCompositionTriangle a b c) :=
  coherentColimitUnitPointedFirstEdgeEndpoint B T k H he ≫
    (leftUnstraighteningMappingVertexMap Q₀ Q₁ (coherentVertexOfHomotopy a)).val ≫
      (leftUnstraighteningMappingVertexMap Q₁ Q₂ (coherentVertexOfHomotopy b)).val

/-- 元の全作用の合成は、元の全パラメータの底の射影を厳密に保つ。 -/
lemma coherentColimitUnitZeroFaceOriginalTargetMap_projection :
    coherentColimitUnitZeroFaceOriginalTargetMap B T k H he S ≫
      leftUnstraighteningProjection Q₂ =
    fst (leftUnstraightening F) (coherentColimitUnitPointedTetrahedronChoice B T k) ≫
      leftUnstraighteningProjection F := by
  rw [coherentColimitUnitZeroFaceOriginalTargetMap, Category.assoc, Category.assoc,
    (leftUnstraighteningMappingVertexMap Q₁ Q₂ (coherentVertexOfHomotopy b)).property,
    (leftUnstraighteningMappingVertexMap Q₀ Q₁ (coherentVertexOfHomotopy a)).property,
    coherentColimitUnitPointedFirstEdgeEndpoint_projection]

/-- 前合成した元の指定三角形の全終点は、元の二作用の同じ native 合成を厳密に表す。 -/
lemma coherentColimitUnitZeroFaceOriginalTriangleLift_target :
    (simplexPrismVertex 2 2 (leftUnstraightening F) ▷
      coherentColimitUnitPointedTetrahedronChoice B T k) ≫
      coherentColimitUnitZeroFaceOriginalTriangleLift B T k H he S =
        coherentColimitUnitZeroFaceOriginalTargetMap B T k H he S ≫
          pullback.fst pointedSpaceProjection Q₂ := by
  let K := coherentColimitUnitPointedTetrahedronChoice B T k
  let f := coherentColimitUnitPointedFirstEdgeEndpoint B T k H he
  have hn : (simplexPrismVertex 2 2 (leftUnstraightening F) ▷ K) ≫
      (α_ (Δ[2] : SSet.{u + 1}) (leftUnstraightening F) K).hom ≫ (Δ[2] ◁ f) =
        f ≫ simplexPrismVertex 2 2 (leftUnstraightening Q₀) := by
    apply SSet.hom_ext
    intro n
    rfl
  simpa only [Category.assoc, functorTrianglePointedLift_target,
    coherentColimitUnitZeroFaceOriginalTriangleLift, coherentColimitUnitZeroFaceOriginalTargetMap,
    K, f] using congrArg (fun z => z ≫ functorTrianglePointedLift S) hn

/-- 前合成した元の指定三角形の全三辺も、同じ実第一辺による元の三辺の前合成。 -/
lemma coherentColimitUnitZeroFaceOriginalTriangleLift_edge (j : Fin 3) :
    ((stdSimplex.δ j ▷ leftUnstraightening F) ▷
      coherentColimitUnitPointedTetrahedronChoice B T k) ≫
      coherentColimitUnitZeroFaceOriginalTriangleLift B T k H he S =
    (α_ (Δ[1] : SSet.{u + 1}) (leftUnstraightening F)
      (coherentColimitUnitPointedTetrahedronChoice B T k)).hom ≫
      (Δ[1] ◁ coherentColimitUnitPointedFirstEdgeEndpoint B T k H he) ≫
      (stdSimplex.δ j ▷ leftUnstraightening Q₀) ≫ functorTrianglePointedLift S := by
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
