module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedFixedFaceOriginal
public import SerrePositivity.InfinityCategories.F2.PointedTriangleFamilyEdgeMap
public import SerrePositivity.InfinityCategories.F2.FunctorTrianglePointedLongWitness

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

local notation "D" => coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS
local notation "w" => unstraighteningMappingTriangleLongWitness F Q₁ Q₂
  (SSet.const (coherentVertexOfHomotopy a)) (SSet.const (coherentVertexOfHomotopy b))
  (SSet.const (coherentVertexOfHomotopy c))
  (CoherentTransformationVertexTriangle.diagram (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.first (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.second (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.long (coherentTriangleOfFunctorTriangle S))

/-- 固定始点の同じ全族比較を、元の三辺へ制限した指定比較。 -/
def coherentColimitUnitPointedFixedFaceEdgeComparison (i : Fin 3) :=
  VertexIso.map (coherentColimitUnitPointedFixedFaceOriginalComparison B T k j hj S hS)
    (pointedTriangleFamilyEdgeMap D i)

/-- 元の指定三角形の定値族の辺は、同じ全選択パラメータを保持した元の辺。 -/
lemma coherentColimitUnitPointedFixedFaceOriginalLift_edge (i : Fin 3) :
    ((stdSimplex.δ i ▷ leftUnstraightening F) ▷ P) ≫
      coherentColimitUnitPointedFixedFaceOriginalLift B T k S =
      fst (Δ[1] ⊗ leftUnstraightening F) P ≫
        (stdSimplex.δ i ▷ leftUnstraightening F) ≫ functorTrianglePointedLift S := by
  rw [coherentColimitUnitPointedFixedFaceOriginalLift, whiskerRight_fst_assoc]

/-- 同じ長辺の標的は、元の指定三角形比較に使った同じ長辺証拠の実制限。 -/
lemma coherentColimitUnitPointedFixedFaceOriginalLift_long :
    (stdSimplex.δ (1 : Fin 3) ▷ (leftUnstraightening F ⊗ P)) ≫
      Iso.inv (α_ Δ[2] (leftUnstraightening F) P) ≫
      coherentColimitUnitPointedFixedFaceOriginalLift B T k S =
      prismParameterRestriction (lift (fst (leftUnstraightening F) P)
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫ (w).prism := by
  calc
    _ = (Δ[1] ◁ fst (leftUnstraightening F) P) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ leftUnstraightening F) ≫
          functorTrianglePointedLift S := by
      apply SSet.hom_ext
      intro n
      rfl
    _ = _ := functorTrianglePointedLift_long S (fst (leftUnstraightening F) P)

end SerrePositivity.InfinityCategories.F2
