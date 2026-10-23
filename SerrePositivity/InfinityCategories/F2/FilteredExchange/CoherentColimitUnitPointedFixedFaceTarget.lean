module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceOriginal
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePointedTarget

/-!
概要：固定始点を持つ元の二面と、元の指定三角形の実持ち上げを比較する。
方針：同じ全初期値の選択空間へ元の二頂点を入れ、長辺へ制限する。
規約：同じ全空間と同じ始点を保持。使われ方：共有面の指定比較を同じ空間で消去。
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
  {F G J Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "P" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "h₀" => coherentColimitUnitPointedFace_initial B T k j hj S.diagram hS

/-- 元の指定三角形の二つの選択済み作用を、同じ全パラメータ上で厳密に合成する。 -/
def coherentColimitUnitPointedFixedFaceOriginalTarget (_S : FunctorCompositionTriangle a b c) :=
  fst (leftUnstraightening F) P ≫
    (leftUnstraighteningMappingVertexMap F Q₁ (coherentVertexOfHomotopy a)).val ≫
    (leftUnstraighteningMappingVertexMap Q₁ Q₂ (coherentVertexOfHomotopy b)).val

/-- 元の二作用の合成は、全選択パラメータの同じ底を保つ。 -/
lemma coherentColimitUnitPointedFixedFaceOriginalTarget_projection :
    coherentColimitUnitPointedFixedFaceOriginalTarget B T k S ≫
      leftUnstraighteningProjection Q₂ =
        fst (leftUnstraightening F) P ≫ leftUnstraighteningProjection F := by
  rw [coherentColimitUnitPointedFixedFaceOriginalTarget, Category.assoc, Category.assoc,
    (leftUnstraighteningMappingVertexMap Q₁ Q₂ (coherentVertexOfHomotopy b)).property,
    (leftUnstraighteningMappingVertexMap F Q₁ (coherentVertexOfHomotopy a)).property]

/-- 元の指定三角形の全終点は、同じ二つの元の native 作用の厳密な合成。 -/
lemma coherentColimitUnitPointedFixedFaceOriginalLift_target :
    (simplexPrismVertex 2 2 (leftUnstraightening F) ▷ P) ≫
      coherentColimitUnitPointedFixedFaceOriginalLift B T k S =
      coherentColimitUnitPointedFixedFaceOriginalTarget B T k S ≫
        pullback.fst pointedSpaceProjection Q₂ := by
  rw [coherentColimitUnitPointedFixedFaceOriginalLift, whiskerRight_fst_assoc,
    functorTrianglePointedLift_target]
  rfl

include hj hS in
/-- 同じ元の全底の終点は、元の全選択パラメータの射影の後の標的図式。 -/
lemma coherentColimitUnitPointedFixedFaceBase_endpoint :
    (simplexPrismVertex 2 2 (leftUnstraightening F) ▷ P) ≫
      ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ P) ≫
      (coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS).diagram =
      (fst (leftUnstraightening F) P ≫ leftUnstraighteningProjection F) ≫ Q₂ := by
  rw [← coherentColimitUnitPointedFixedFaceOriginalLift_projection B T k j hj S hS,
    ← Category.assoc, coherentColimitUnitPointedFixedFaceOriginalLift_target,
    Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun z => z ≫ Q₂)
    (coherentColimitUnitPointedFixedFaceOriginalTarget_projection B T k S)

end SerrePositivity.InfinityCategories.F2
