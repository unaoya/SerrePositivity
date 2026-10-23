module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceFamily

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

/-- 元の指定三角形の実持ち上げを、元の全三単体の全選択で定値な族として保つ。 -/
def coherentColimitUnitPointedFixedFaceOriginalLift :=
  fst (Δ[2] ⊗ leftUnstraightening F) P ≫ functorTrianglePointedLift S

/-- 元の指定三角形の定値族は、元の実二面と同じ全初期値を厳密に保持する。 -/
lemma coherentColimitUnitPointedFixedFaceOriginalLift_boundary :
    ((scaffoldFirstVertex 2 ▷ leftUnstraightening F) ▷ P) ≫
      coherentColimitUnitPointedFixedFaceOriginalLift B T k S =
        (coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS).boundary := by
  rw [coherentColimitUnitPointedFixedFaceOriginalLift, ← Category.assoc,
    whiskerRight_fst, Category.assoc, functorTrianglePointedLift_start]
  rfl

/-- 元の指定三角形の定値族は、同じ全選択パラメータ上で元の全底を保つ。 -/
lemma coherentColimitUnitPointedFixedFaceOriginalLift_projection :
    coherentColimitUnitPointedFixedFaceOriginalLift B T k S ≫ pointedSpaceProjection =
      ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ P) ≫
        (coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS).diagram := by
  rw [coherentColimitUnitPointedFixedFaceOriginalLift, Category.assoc,
    functorTrianglePointedLift_projection]
  change _ = _ ≫ fst _ _ ≫ functorSimplexDiagram S.diagram
  rw [whiskerRight_fst_assoc]

/-- 元の実二面と元の指定三角形を、全選択・全初期値固定の同じ延長空間で比較する。 -/
def coherentColimitUnitPointedFixedFaceOriginalComparison :=
  pointedPrismFamilyComparison (coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS)
    (scaffoldFirstVertex_leftAnodyne 2)
    (coherentColimitUnitPointedFixedFaceLift B T k j)
    (coherentColimitUnitPointedFixedFaceOriginalLift B T k S)
    (coherentColimitUnitPointedFixedFaceLift_boundary B T k j hj S hS)
    (coherentColimitUnitPointedFixedFaceLift_projection B T k j hj S hS)
    (coherentColimitUnitPointedFixedFaceOriginalLift_boundary B T k j hj S hS)
    (coherentColimitUnitPointedFixedFaceOriginalLift_projection B T k j hj S hS)

end SerrePositivity.InfinityCategories.F2
